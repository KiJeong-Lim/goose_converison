(* autogenerated from github.com/mit-pdos/go-journal/jrnl *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.go_journal.addr.
From Goose Require github_com.mit_pdos.go_journal.buf.
From Goose Require github_com.mit_pdos.go_journal.obj.
From Goose Require github_com.mit_pdos.go_journal.util.

From Perennial.goose_lang Require Import ffi.disk_prelude.

(* Package jrnl is the top-level journal API.

   It provides atomic operations that are buffered locally and manipulate
   objects via buffers of type *buf.Buf.

   The caller uses this interface by beginning an operation Op,
   reading/writing within the transaction, and finally committing the buffered
   transaction.

   Note that while the API has reads and writes, these are not the usual database
   read/write transactions. Only writes are made atomic and visible atomically;
   reads are cached on first read. Thus to use this library the file
   system in practice locks (sub-block) objects before using them in an
   operation. This is necessary so that loaded objects are read from a consistent
   view.

   Operations support asynchronous durability by setting wait=false in
   CommitWait, which results in an "unstable" operation. An unstable operation is
   made visible atomically to other threads, including across crashes, but if the
   system crashes the latest unstable operations can be lost. To guarantee that a
   particular operation is durable, call Flush on the underlying *obj.Log (which
   flushes all transactions).

   Objects have sizes. Implicit in the code is that there is a static "schema"
   that determines the disk layout: each block has objects of a particular size,
   and all sizes used fit an integer number of objects in a block. This schema
   guarantees that objects never overlap, as long as operations involving an
   addr.Addr use the correct size for that block number.

   A file system can realize this schema fairly simply, since the disk is
   partitioned into inodes, data blocks, and bitmap allocators for each (sized
   appropriately), all allocated statically. *)

Definition LogBlocks : expr := #511.

Definition LogBytes : expr := #4096 * #511.

(* Op is an in-progress journal operation.

   Call CommitWait to persist the operation's writes.
   To abort the operation simply stop using it. *)
Definition Op := struct.decl [
  "log" :: ptrT;
  "bufs" :: ptrT
].

(* Begin starts a local journal operation with no writes from a global object
   manager. *)
Definition Begin: val :=
  rec: "Begin" "log" :=
    let: "trans" := struct.new Op [
      "log" ::= "log";
      "bufs" ::= buf.MkBufMap #()
    ] in
    util.DPrintf #3 (#(str"Begin: %v
    ")) #();;
    "trans".

Definition Op__ReadBuf: val :=
  rec: "Op__ReadBuf" "op" "addr" "sz" :=
    let: "b" := buf.BufMap__Lookup (struct.loadF Op "bufs" "op") "addr" in
    (if: ("b" = #null)
    then
      let: "buf" := obj.Log__Load (struct.loadF Op "log" "op") "addr" "sz" in
      buf.BufMap__Insert (struct.loadF Op "bufs" "op") "buf";;
      buf.BufMap__Lookup (struct.loadF Op "bufs" "op") "addr"
    else "b").

(* OverWrite writes an object to addr *)
Definition Op__OverWrite: val :=
  rec: "Op__OverWrite" "op" "addr" "sz" "data" :=
    let: "b" := ref_to ptrT (buf.BufMap__Lookup (struct.loadF Op "bufs" "op") "addr") in
    (if: (![ptrT] "b" = #null)
    then
      "b" <-[ptrT] buf.MkBuf "addr" "sz" "data";;
      buf.Buf__SetDirty (![ptrT] "b");;
      buf.BufMap__Insert (struct.loadF Op "bufs" "op") (![ptrT] "b");;
      #()
    else
      (if: "sz" ≠ struct.loadF buf.Buf "Sz" (![ptrT] "b")
      then Panic "overwrite"
      else #());;
      struct.storeF buf.Buf "Data" (![ptrT] "b") "data";;
      buf.Buf__SetDirty (![ptrT] "b");;
      #()).

(* NDirty reports an upper bound on the size of this transaction when committed.

   The caller cannot rely on any particular properties of this function for
   safety. *)
Definition Op__NDirty: val :=
  rec: "Op__NDirty" "op" :=
    buf.BufMap__Ndirty (struct.loadF Op "bufs" "op").

(* CommitWait commits the writes in the transaction to disk.

   If CommitWait returns false, the transaction failed and had no logical effect.
   This can happen, for example, if the transaction is too big to fit in the
   on-disk journal.

   wait=true is a synchronous commit, which is durable as soon as CommitWait
   returns.

   wait=false is an asynchronous commit, which can be made durable later with
   Flush. *)
Definition Op__CommitWait: val :=
  rec: "Op__CommitWait" "op" "wait" :=
    util.DPrintf #3 (#(str"Commit %p w %v
    ")) #();;
    let: "ok" := obj.Log__CommitWait (struct.loadF Op "log" "op") (buf.BufMap__DirtyBufs (struct.loadF Op "bufs" "op")) "wait" in
    "ok".
