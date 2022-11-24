(* autogenerated from github.com/mit-pdos/go-nfsd/kvs *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.go_journal.addr.
From Goose Require github_com.mit_pdos.go_journal.common.
From Goose Require github_com.mit_pdos.go_journal.jrnl.
From Goose Require github_com.mit_pdos.go_journal.obj.
From Goose Require github_com.mit_pdos.go_journal.util.

From Perennial.goose_lang Require Import ffi.disk_prelude.

Definition DISKNAME : expr := #(str"goose_kvs.img").

Definition KVS := struct.decl [
  "sz" :: uint64T;
  "log" :: ptrT
].

Definition KVPair := struct.decl [
  "Key" :: uint64T;
  "Val" :: slice.T byteT
].

Definition MkKVS: val :=
  rec: "MkKVS" "d" "sz" :=
    let: "log" := obj.MkLog "d" in
    let: "kvs" := struct.new KVS [
      "sz" ::= "sz";
      "log" ::= "log"
    ] in
    "kvs".

Definition KVS__MultiPut: val :=
  rec: "KVS__MultiPut" "kvs" "pairs" :=
    let: "op" := jrnl.Begin (struct.loadF KVS "log" "kvs") in
    ForSlice (struct.t KVPair) <> "p" "pairs"
      ((if: (struct.get KVPair "Key" "p" ≥ struct.loadF KVS "sz" "kvs") || (struct.get KVPair "Key" "p" < common.LOGSIZE)
      then Panic "oops"
      else #());;
      let: "akey" := addr.MkAddr (struct.get KVPair "Key" "p") #0 in
      jrnl.Op__OverWrite "op" "akey" common.NBITBLOCK (struct.get KVPair "Val" "p"));;
    let: "ok" := jrnl.Op__CommitWait "op" #true in
    "ok".

Definition KVS__Get: val :=
  rec: "KVS__Get" "kvs" "key" :=
    (if: ("key" > struct.loadF KVS "sz" "kvs") || ("key" < common.LOGSIZE)
    then Panic "oops"
    else #());;
    let: "op" := jrnl.Begin (struct.loadF KVS "log" "kvs") in
    let: "akey" := addr.MkAddr "key" #0 in
    let: "data" := util.CloneByteSlice (struct.loadF buf.Buf "Data" (jrnl.Op__ReadBuf "op" "akey" common.NBITBLOCK)) in
    let: "ok" := jrnl.Op__CommitWait "op" #true in
    (struct.new KVPair [
       "Key" ::= "key";
       "Val" ::= "data"
     ], "ok").

Definition KVS__Delete: val :=
  rec: "KVS__Delete" "kvs" :=
    obj.Log__Shutdown (struct.loadF KVS "log" "kvs");;
    #().
