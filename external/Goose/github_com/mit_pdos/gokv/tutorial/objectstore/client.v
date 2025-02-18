(* autogenerated from github.com/mit-pdos/gokv/tutorial/objectstore/client *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.gokv.tutorial.objectstore.chunk.
From Goose Require github_com.mit_pdos.gokv.tutorial.objectstore.chunk.writechunk_gk.
From Goose Require github_com.mit_pdos.gokv.tutorial.objectstore.dir.
From Goose Require github_com.mit_pdos.gokv.tutorial.objectstore.dir.finishwrite_gk.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition Clerk := struct.decl [
  "dCk" :: ptrT;
  "chCk" :: ptrT
].

Definition Writer := struct.decl [
  "writeId" :: uint64T;
  "index" :: uint64T;
  "keyname" :: stringT;
  "wg" :: ptrT;
  "ck" :: ptrT;
  "chunkAddrs" :: slice.T uint64T
].

Definition Clerk__PrepareWrite: val :=
  rec: "Clerk__PrepareWrite" "ck" "keyname" :=
    let: "w" := dir.Clerk__PrepareWrite (struct.loadF Clerk "dCk" "ck") in
    struct.new Writer [
      "writeId" ::= struct.get dir.PreparedWrite "Id" "w";
      "index" ::= #0;
      "keyname" ::= "keyname";
      "chunkAddrs" ::= struct.get dir.PreparedWrite "ChunkAddrs" "w"
    ].

Definition Writer__AppendChunk: val :=
  rec: "Writer__AppendChunk" "w" "data" :=
    waitgroup.Add (struct.loadF Writer "wg" "w") #1;;
    let: "index" := struct.loadF Writer "index" "w" in
    struct.storeF Writer "index" "w" ((struct.loadF Writer "index" "w") + #1);;
    Fork (let: "addr" := SliceGet uint64T (struct.loadF Writer "chunkAddrs" "w") ("index" `rem` (slice.len (struct.loadF Writer "chunkAddrs" "w"))) in
          let: "args" := struct.mk writechunk_gk.S [
            "WriteId" ::= struct.loadF Writer "writeId" "w";
            "Chunk" ::= "data";
            "Index" ::= "index"
          ] in
          chunk.ClerkPool__WriteChunk (struct.loadF Clerk "chCk" (struct.loadF Writer "ck" "w")) "addr" "args";;
          waitgroup.Done (struct.loadF Writer "wg" "w"));;
    #().

Definition Writer__Done: val :=
  rec: "Writer__Done" "w" :=
    waitgroup.Wait (struct.loadF Writer "wg" "w");;
    dir.Clerk__FinishWrite (struct.loadF Clerk "dCk" (struct.loadF Writer "ck" "w")) (struct.mk finishwrite_gk.S [
      "WriteId" ::= struct.loadF Writer "writeId" "w";
      "Keyname" ::= struct.loadF Writer "keyname" "w"
    ]);;
    #().

Definition Reader := struct.decl [
  "chunkHandles" :: slice.T (struct.t dir.ChunkHandle);
  "index" :: uint64T;
  "ck" :: ptrT
].

Definition Clerk__PrepareRead: val :=
  rec: "Clerk__PrepareRead" "ck" "keyname" :=
    struct.new Reader [
      "chunkHandles" ::= struct.get dir.PreparedRead "Handles" (dir.Clerk__PrepareRead (struct.loadF Clerk "dCk" "ck") "keyname");
      "index" ::= #0
    ].

Definition Reader__GetNextChunk: val :=
  rec: "Reader__GetNextChunk" "r" :=
    (if: (struct.loadF Reader "index" "r") ≥ (slice.len (struct.loadF Reader "chunkHandles" "r"))
    then (#false, slice.nil)
    else
      let: "handle" := SliceGet (struct.t dir.ChunkHandle) (struct.loadF Reader "chunkHandles" "r") (struct.loadF Reader "index" "r") in
      struct.storeF Reader "index" "r" ((struct.loadF Reader "index" "r") + #1);;
      (#true, chunk.ClerkPool__GetChunk (struct.loadF Clerk "chCk" (struct.loadF Reader "ck" "r")) (struct.get dir.ChunkHandle "Addr" "handle") (struct.get dir.ChunkHandle "ContentHash" "handle"))).
