From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip Require Import base.
From Perennial.program_proof.rsm Require Import serialize.

Definition encode_string (x : byte_string) : list u8 :=
  u64_le (U64 (length x)) ++ x.

Definition encode_strings_xlen (xs : list byte_string) : list u8 :=
  serialize encode_string xs.

Definition encode_strings (xs : list byte_string) : list u8 :=
  u64_le (U64 (length xs)) ++ encode_strings_xlen xs.

Lemma encode_strings_xlen_snoc xs x :
  encode_strings_xlen (xs ++ [x]) = encode_strings_xlen xs ++ encode_string x.
Proof. by rewrite /encode_strings_xlen serialize_snoc. Qed.

Lemma encode_strings_xlen_cons xs x :
  encode_strings_xlen (x :: xs) = encode_string x ++ encode_strings_xlen xs.
Proof. by rewrite /encode_strings_xlen serialize_cons. Qed.

Lemma encode_strings_xlen_length_inv xs n :
  (length (encode_strings_xlen xs) ≤ n)%nat ->
  (length xs ≤ n)%nat.
Proof.
  rewrite /encode_strings_xlen.
  intros Hlen.
  apply (serialize_length_inv encode_string).
  { intros x. by destruct (nil_or_length_pos (encode_string x)). }
  done.
Qed.

Lemma encode_strings_length_inv xs n :
  (length (encode_strings xs) ≤ n)%nat ->
  (length xs ≤ n)%nat.
Proof.
  rewrite /encode_strings length_app.
  intros Hn.
  pose proof (encode_strings_xlen_length_inv xs n) as Hlen.
  lia.
Qed.

Definition encode_dbval (x : dbval) : list u8 :=
  match x with
  | Some v => [U8 1] ++ encode_string v
  | None => [U8 0]
  end.

Definition encode_dbmod (x : dbmod) : list u8 :=
  encode_string x.1 ++ encode_dbval x.2.

Definition encode_dbmods_xlen (xs : list dbmod) : list u8 :=
  serialize encode_dbmod xs.

Definition encode_dbmods (xs : list dbmod) : list u8 :=
  u64_le (U64 (length xs)) ++ encode_dbmods_xlen xs.

Lemma encode_dbmods_xlen_snoc xs x :
  encode_dbmods_xlen (xs ++ [x]) = encode_dbmods_xlen xs ++ encode_dbmod x.
Proof. by rewrite /encode_dbmods_xlen serialize_snoc. Qed.

Lemma encode_dbmods_xlen_cons xs x :
  encode_dbmods_xlen (x :: xs) = encode_dbmod x ++ encode_dbmods_xlen xs.
Proof. by rewrite /encode_dbmods_xlen serialize_cons. Qed.

Lemma encode_dbmods_xlen_length_inv xs n :
  (length (encode_dbmods_xlen xs) ≤ n)%nat ->
  (length xs ≤ n)%nat.
Proof.
  rewrite /encode_dbmods_xlen.
  intros Hlen.
  apply (serialize_length_inv encode_dbmod).
  { intros x. by destruct (nil_or_length_pos (encode_dbmod x)). }
  done.
Qed.

Lemma encode_dbmods_length_inv xs n :
  (length (encode_dbmods xs) ≤ n)%nat ->
  (length xs ≤ n)%nat.
Proof.
  rewrite /encode_dbmods length_app.
  intros Hn.
  pose proof (encode_dbmods_xlen_length_inv xs n) as Hlen.
  lia.
Qed.

Definition encode_dbmap (m : dbmap) (data : list u8) :=
  ∃ xs, data = encode_dbmods xs ∧ xs ≡ₚ map_to_list m.

Definition encode_dbpver (x : dbpver) : list u8 :=
  u64_le x.1 ++ encode_dbval x.2.
