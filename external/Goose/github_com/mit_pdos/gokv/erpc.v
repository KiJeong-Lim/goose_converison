(* autogenerated from github.com/mit-pdos/gokv/erpc *)
From Perennial.goose_lang Require Import prelude.
Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

From Goose Require github_com.tchajed.marshal.

(* Implements "exactly-once RPCs" with a reply table. *)

Definition Server := struct.decl [
  "mu" :: ptrT;
  "lastSeq" :: mapT uint64T;
  "lastReply" :: mapT (slice.T byteT);
  "lastCID" :: uint64T
].

Definition Server__HandleRequest: val :=
  rec: "Server__HandleRequest" "t" "handler" :=
    (λ: "raw_args" "reply",
      let: "dec" := marshal.NewDec "raw_args" in
      let: "cid" := marshal.Dec__GetInt "dec" in
      let: "seq" := marshal.Dec__GetInt "dec" in
      lock.acquire (struct.loadF Server "mu" "t");;
      let: ("last", "ok") := MapGet (struct.loadF Server "lastSeq" "t") "cid" in
      (if: "ok" && ("seq" ≤ "last")
      then
        "reply" <-[slice.T byteT] Fst (MapGet (struct.loadF Server "lastReply" "t") "cid");;
        lock.release (struct.loadF Server "mu" "t");;
        #()
      else
        "handler" (marshal.Dec__GetRemainingBytes "dec") "reply";;
        MapInsert (struct.loadF Server "lastSeq" "t") "cid" "seq";;
        MapInsert (struct.loadF Server "lastReply" "t") "cid" (![slice.T byteT] "reply");;
        lock.release (struct.loadF Server "mu" "t");;
        #())
      ).

Definition Server__GetFreshCID: val :=
  rec: "Server__GetFreshCID" "t" :=
    lock.acquire (struct.loadF Server "mu" "t");;
    struct.storeF Server "lastCID" "t" (struct.loadF Server "lastCID" "t" + #1);;
    let: "ret" := struct.loadF Server "lastCID" "t" in
    lock.release (struct.loadF Server "mu" "t");;
    "ret".

Definition MakeServer: val :=
  rec: "MakeServer" <> :=
    let: "t" := struct.alloc Server (zero_val (struct.t Server)) in
    struct.storeF Server "lastReply" "t" (NewMap (slice.T byteT) #());;
    struct.storeF Server "lastSeq" "t" (NewMap uint64T #());;
    struct.storeF Server "lastCID" "t" #0;;
    struct.storeF Server "mu" "t" (lock.new #());;
    "t".

Definition Client := struct.decl [
  "cid" :: uint64T;
  "seq" :: uint64T
].

Definition Client__NewRequest: val :=
  rec: "Client__NewRequest" "c" "request" :=
    struct.storeF Client "seq" "c" (struct.loadF Client "seq" "c" + #1);;
    let: "enc" := marshal.NewEnc (#2 * #8 + slice.len "request") in
    marshal.Enc__PutInt "enc" (struct.loadF Client "cid" "c");;
    marshal.Enc__PutInt "enc" (struct.loadF Client "seq" "c");;
    marshal.Enc__PutBytes "enc" "request";;
    marshal.Enc__Finish "enc".

Definition MakeClient: val :=
  rec: "MakeClient" "cid" :=
    let: "c" := struct.alloc Client (zero_val (struct.t Client)) in
    struct.storeF Client "cid" "c" "cid";;
    struct.storeF Client "seq" "c" #0;;
    "c".

End code.
