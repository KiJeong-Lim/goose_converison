(* autogenerated from github.com/mit-pdos/gokv/vrsm/e *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.tchajed.marshal.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Notation Error := uint64T (only parsing).

Definition None : expr := #0.

Definition Stale : expr := #1.

Definition OutOfOrder : expr := #2.

Definition Timeout : expr := #3.

Definition EmptyConfig : expr := #4.

Definition NotLeader : expr := #5.

Definition Sealed : expr := #6.

Definition LeaseExpired : expr := #7.

Definition Leased : expr := #8.

Definition EncodeError: val :=
  rec: "EncodeError" "err" :=
    marshal.WriteInt (NewSliceWithCap byteT #0 #8) "err".

Definition DecodeError: val :=
  rec: "DecodeError" "enc" :=
    let: ("err", <>) := marshal.ReadInt "enc" in
    "err".

End code.
