(* autogenerated from github.com/mit-pdos/gokv/tutorial/objectstore/chunk *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.gokv.connman.
From Goose Require github_com.mit_pdos.gokv.tutorial.objectstore.dir.
From Goose Require github_com.mit_pdos.gokv.urpc.
From Perennial.goose_lang.trusted Require Import github_com.mit_pdos.gokv.trusted_hash.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* 0data.go *)

(* WriteID from client.go *)

Notation WriteID := uint64T (only parsing).

Definition WriteChunkArgs := struct.decl [
  "WriteId" :: WriteID;
  "Chunk" :: slice.T byteT;
  "Index" :: uint64T
].

Definition MarshalWriteChunkArgs: val :=
  rec: "MarshalWriteChunkArgs" "args" :=
    Panic "TODO: marshalling";;
    #().

Definition ParseWriteChunkArgs: val :=
  rec: "ParseWriteChunkArgs" "data" :=
    Panic "TODO: marshalling";;
    #().

(* client.go *)

Definition WriteChunkId : expr := #1.

Definition GetChunkId : expr := #2.

Definition ClerkPool := struct.decl [
  "cm" :: ptrT
].

Definition ClerkPool__WriteChunk: val :=
  rec: "ClerkPool__WriteChunk" "ck" "addr" "args" :=
    let: "req" := MarshalWriteChunkArgs "args" in
    let: "reply" := ref (zero_val (slice.T byteT)) in
    connman.ConnMan__CallAtLeastOnce (struct.loadF ClerkPool "cm" "ck") "addr" WriteChunkId "req" "reply" #100;;
    #().

Definition ClerkPool__GetChunk: val :=
  rec: "ClerkPool__GetChunk" "ck" "addr" "content_hash" :=
    let: "req" := StringToBytes "content_hash" in
    let: "reply" := ref (zero_val (slice.T byteT)) in
    connman.ConnMan__CallAtLeastOnce (struct.loadF ClerkPool "cm" "ck") "addr" GetChunkId "req" "reply" #100;;
    ![slice.T byteT] "reply".

(* server.go *)

Definition Server := struct.decl [
  "m" :: ptrT;
  "chunks" :: mapT (slice.T byteT);
  "dir" :: ptrT;
  "me" :: uint64T
].

Definition Server__WriteChunk: val :=
  rec: "Server__WriteChunk" "s" "args" :=
    let: "content_hash" := trusted_hash.Hash (struct.get WriteChunkArgs "Chunk" "args") in
    lock.acquire (struct.loadF Server "m" "s");;
    MapInsert (struct.loadF Server "chunks" "s") "content_hash" (struct.get WriteChunkArgs "Chunk" "args");;
    lock.release (struct.loadF Server "m" "s");;
    dir.Clerk__RecordChunk (struct.loadF Server "dir" "s") (struct.mk dir.RecordChunkArgs [
      "WriteId" ::= struct.get WriteChunkArgs "WriteId" "args";
      "Server" ::= struct.loadF Server "me" "s";
      "ContentHash" ::= "content_hash";
      "Index" ::= struct.get WriteChunkArgs "Index" "args"
    ]);;
    #().

Definition Server__GetChunk: val :=
  rec: "Server__GetChunk" "s" "content_hash" :=
    lock.acquire (struct.loadF Server "m" "s");;
    let: "data" := Fst (MapGet (struct.loadF Server "chunks" "s") "content_hash") in
    lock.release (struct.loadF Server "m" "s");;
    "data".

Definition StartServer: val :=
  rec: "StartServer" "me" "dir_addr" :=
    let: "dir" := dir.MakeClerk "dir_addr" in
    let: "s" := struct.new Server [
      "m" ::= lock.new #();
      "chunks" ::= NewMap stringT (slice.T byteT) #();
      "dir" ::= "dir";
      "me" ::= "me"
    ] in
    let: "handlers" := NewMap uint64T ((slice.T byteT) -> ptrT -> unitT)%ht #() in
    MapInsert "handlers" WriteChunkId (λ: "req" "reply",
      let: "args" := ParseWriteChunkArgs "req" in
      Server__WriteChunk "s" "args";;
      "reply" <-[slice.T byteT] (NewSlice byteT #0);;
      #()
      );;
    MapInsert "handlers" GetChunkId (λ: "req" "reply",
      let: "args" := StringFromBytes "req" in
      let: "ret" := Server__GetChunk "s" "args" in
      "reply" <-[slice.T byteT] "ret";;
      #()
      );;
    let: "server" := urpc.MakeServer "handlers" in
    urpc.Server__Serve "server" "me";;
    #().
