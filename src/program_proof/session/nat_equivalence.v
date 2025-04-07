From Perennial.program_proof.session Require Export coq_session coq_session_client.

Reserved Infix "=~=" (at level 70, no associativity).

Class Similarity (A : Type) (B : Type) : Type :=
  is_similar_to (x : A) (y : B) : Prop.

Infix "=~=" := is_similar_to.

Inductive list_corres {A : Type} {B : Type} {SIM : Similarity A B} : Similarity (list A) (list B) :=
  | nil_corres
    : [] =~= []
  | cons_corres x y xs ys
    (head_corres : x =~= y)
    (tail_corres : xs =~= ys)
    : x :: xs =~= y :: ys.

#[global]
Instance Similarity_list_list {A : Type} {B : Type} (SIM : Similarity A B) : Similarity (list A) (list B) :=
  @list_corres A B SIM.

#[global]
Instance Similarity_u64_nat : Similarity u64 nat :=
  fun ux => fun nx => (nx = uint.nat ux)%nat /\ (uint.Z ux >= 0 /\ uint.Z ux < 2^32)%Z.
