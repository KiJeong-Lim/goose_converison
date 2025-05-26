From Goose.github_com.session Require Export server.
From Goose.github_com.session Require Export client.
From Perennial.program_proof Require Export std_proof grove_prelude.

#[local] Obligation Tactic := intros.

Create HintDb session_hints.

Module SessionPrelude.

  Section EQ_EM_implies_EQ_PIRREL.

    Context {A : Type}.

    Definition eq_reflexivity (x1 : A) : x1 = x1 :=
      @eq_refl A x1.

    Definition eq_symmetry (x1 : A) (x2 : A) (x1_eq_x2 : x1 = x2) : x2 = x1 :=
      @eq_ind A x1 (fun x : A => x = x1) (@eq_refl A x1) x2 x1_eq_x2.

    Definition eq_transitivity (x1 : A) (x2 : A) (x3 : A) (x1_eq_x2 : x1 = x2) (x2_eq_x3 : x2 = x3) : x1 = x3 :=
      @eq_ind A x2 (fun x : A => x1 = x) x1_eq_x2 x3 x2_eq_x3.

    Lemma eq_round_trip (x : A) (y : A)
      (x_eq_y : x = y)
      : eq_transitivity y x y (eq_symmetry x y x_eq_y) x_eq_y = eq_reflexivity y.
    Proof.
      destruct x_eq_y; reflexivity.
    Defined.

    Variable x : A.

    Section ABSTRACT_FORM.

      Variable eq_encoder : forall y : A, x = y -> x = y.

      Let eq_decoder (y : A) : x = y -> x = y :=
        eq_transitivity x x y (eq_symmetry x x (eq_encoder x (eq_reflexivity x))).

      Lemma eq_decoder_correct (y : A)
        (x_eq_y : x = y)
        : eq_decoder y (eq_encoder y x_eq_y) = x_eq_y.
      Proof.
        unfold eq_decoder. destruct x_eq_y. rewrite eq_round_trip. reflexivity.
      Defined.

      Hypothesis indistinguishable : forall y : A, forall H_eq1 : x = y, forall H_eq2 : x = y, eq_encoder y H_eq1 = eq_encoder y H_eq2.

      Lemma eq_pirrel_from_eq_em (y : A)
        (H_eq1 : x = y)
        (H_eq2 : x = y)
        : H_eq1 = H_eq2.
      Proof using indistinguishable.
        rewrite <- eq_decoder_correct with (x_eq_y := H_eq1). rewrite <- eq_decoder_correct with (x_eq_y := H_eq2). f_equal. eapply indistinguishable.
      Defined.

    End ABSTRACT_FORM.

    Hypothesis eq_em : forall y : A, x = y \/ ~ x = y.

    Let eq_encoder (y : A) (x_eq_y : x = y) : x = y :=
      match eq_em y with
      | or_introl H_eq => H_eq
      | or_intror H_ne => False_ind (x = y) (H_ne x_eq_y)
      end.

    Lemma eq_encoder_good
      (x_eq_x : x = x)
      : eq_encoder x x_eq_x = eq_encoder x (eq_reflexivity x).
    Proof using eq_em eq_encoder.
      unfold eq_encoder. destruct (eq_em x) as [H_eq | H_ne]; [reflexivity | contradiction (H_ne x_eq_x)].
    Defined.

    Theorem eq_em_implies_eq_pirrel (y : A)
      (EQ1 : x = y)
      (EQ2 : x = y)
      : EQ1 = EQ2.
    Proof using eq_em eq_encoder.
      revert y EQ1 EQ2. eapply eq_pirrel_from_eq_em with (eq_encoder := eq_encoder). intros. destruct H_eq2. eapply eq_encoder_good.
    Defined.

  End EQ_EM_implies_EQ_PIRREL.

  Section NAT_LEMMA.

    Open Scope nat_scope.

    Lemma nat_le_0_n {n : nat}
      : (0 <= n).
    Proof.
      induction n as [ | n IH].
      - eapply le_n.
      - eapply le_S. exact IH.
    Defined.

    Lemma nat_le_n_n {n : nat}
      : (n <= n).
    Proof.
      eapply le_n.
    Defined.

    Lemma le_gt_dec (n : nat) (m : nat)
      : { n <= m } + { n > m }.
    Proof.
      revert m. induction n as [ | n IH].
      - left. word.
      - destruct m as [ | m]; simpl.
        + right. word.
        + pose proof (IH m) as [LE | GT].
          * left. word.
          * right. word.
    Qed.

    Lemma case_le_n {n : nat} (phi : n <= n -> Prop)
      (phi_le_n : phi (@le_n n))
      : forall H_le : n <= n, phi H_le.
    Proof.
      intros H_le. refine ((fun claim : forall EQ : n = n, phi (eq_ind n (fun m' : nat => n <= m') H_le n EQ) => claim eq_refl) (match H_le in le _ m return forall H_obs : m = n, phi (@eq_ind _ _ (fun m' : nat => n <= m') H_le _ H_obs) with @le_n _ => fun H_obs: n = n => _ | @le_S _ m' H_le' => fun H_obs: S m' = n => _ end)).
      - rewrite -> eq_em_implies_eq_pirrel with (EQ1 := H_obs) (EQ2 := eq_refl); try word. exact (phi_le_n).
      - lia.
    Qed.

    Lemma case_le_S {n : nat} {m : nat} (H_le : m <= n) (phi : m <= S n -> Prop)
      (phi_le_S : forall H_le' : m <= n, phi (@le_S m n H_le'))
      : forall H_lt : m <= S n, phi H_lt.
    Proof.
      intros H_lt. refine ((fun claim : forall EQ : S n = S n, phi (eq_ind (S n) (fun n' : nat => m <= n') H_lt (S n) EQ) => claim eq_refl) (match H_lt in le _ n' return forall H_obs : n' = S n, phi (@eq_ind _ _ (fun n' => m <= n') H_lt _ H_obs) with @le_n _ => fun H_obs : m = S n => _ | @le_S _ m' H_le' => fun H_obs : S m' = S n => _ end)).
      - lia.
      - assert (m' = n) as H_eq by now apply f_equal with (f := pred) in H_obs. subst m'. rewrite -> eq_em_implies_eq_pirrel with (EQ1 := H_obs) (EQ2 := eq_refl); try word. exact (phi_le_S H_le').
    Qed.

    Theorem le_proof_irrel {n : nat} {m : nat}
      (LE1 : (n <= m)%nat)
      (LE2 : (n <= m)%nat)
      : LE1 = LE2.
    Proof.
      assert (m = (m - n) + n)%nat as claim by lia. remember (m - n)%nat as k eqn: H_eq in claim. clear H_eq. revert n m LE1 LE2 claim. induction k as [ | k IH]; simpl.
      - intros. subst m. induction LE1 using case_le_n. induction LE2 using case_le_n. reflexivity.
      - intros. subst m. assert (n <= k + n) as LE by lia. induction LE1 using (case_le_S LE). induction LE2 using (case_le_S LE). eapply f_equal. eapply IH. reflexivity.
    Qed.

  End NAT_LEMMA.

  Section MORE_LIST_LEMMAS.

    Context {A : Type}.

    Lemma list_ext (xs : list A) (ys : list A)
      (LENGTH : length xs = length ys)
      (LOOKUP : ∀ i : nat, ∀ x : A, ∀ y : A, (xs !! i = Some x /\ ys !! i = Some y) -> x = y)
      : xs = ys.
    Proof.
      generalize dependent ys. induction xs as [ | x xs IH], ys as [ | y ys]; simpl; intros; try congruence. f_equal.
      - eapply LOOKUP with (i := 0%nat); simpl; tauto.
      - eapply IH. { word. }
        intros i x1 y1 [H_x1 H_y1]. eapply LOOKUP with (i := S i); simpl; tauto.
    Qed.

    Lemma rev_app (l1 : list A) (l2 : list A)
      : rev (l1 ++ l2) = (rev l2 ++ rev l1).
    Proof.
      induction l1 as [ | x1 l1 IH]; simpl.
      - rewrite app_nil_r. reflexivity.
      - rewrite IH. now rewrite <- app_assoc.
    Qed.

    Lemma rev_dual (P : list A -> Prop)
      (DUAL : ∀ l : list A, P (rev l))
      : ∀ l : list A, P l.
    Proof.
      induction l as [ | x l _] using rev_ind.
      - eapply DUAL with (l := []).
      - rewrite <- rev_involutive with (l := l). eapply DUAL with (l := (x :: rev l)).
    Qed.

    Lemma rev_inj (l1 : list A) (l2 : list A)
      (EQ : rev l1 = rev l2)
      : l1 = l2.
    Proof.
      rewrite <- rev_involutive with (l := l1). rewrite <- rev_involutive with (l := l2). congruence.
    Qed.

    Lemma app_cancel_l (prefix : list A) (suffix1 : list A) (suffix2 : list A)
      (EQ : prefix ++ suffix1 = prefix ++ suffix2)
      : suffix1 = suffix2.
    Proof.
      revert suffix1 suffix2 EQ; induction prefix as [ | x xs IH]; simpl; intros; eauto. eapply IH; congruence.
    Qed.

    Lemma app_cancel_r (prefix1 : list A) (prefix2 : list A) (suffix : list A)
      (EQ : prefix1 ++ suffix = prefix2 ++ suffix)
      : prefix1 = prefix2.
    Proof.
      revert prefix1 prefix2 EQ. induction suffix as [suffix] using rev_dual.
      induction prefix1 as [prefix1] using rev_dual. induction prefix2 as [prefix2] using rev_dual.
      do 2 rewrite <- rev_app. intros EQ. apply rev_inj in EQ. apply app_cancel_l in EQ. congruence.
    Qed.

    Lemma forallb_spec (p : A -> bool) (xs : list A)
      : forall b, forallb p xs = b <-> (if b then forall x, In x xs -> p x = true else exists x, In x xs /\ p x = false).
    Proof with try now firstorder.
      intros [ | ]; [exact (forallb_forall p xs) | induction xs as [ | x xs IH]; simpl in *]...
      rewrite andb_false_iff; firstorder; subst...
    Qed.

    Lemma In_lookup (xs : list A) (x : A)
      (IN : In x xs)
      : exists n : nat, xs !! n = Some x /\ n < length xs.
    Proof with try (word || done).
      revert x IN; induction xs as [ | x1 xs IH]; simpl; intros x0 IN... destruct IN as [<- | IN].
      - exists 0%nat...
      - pose proof (IH x0 IN) as (n & EQ & LE). exists (S n). split...
    Qed.

    Lemma lookup_In (xs : list A) (x : A) (n : nat)
      (LOOKUP : xs !! n = Some x)
      : In x xs.
    Proof with try done.
      revert xs n x LOOKUP; induction xs as [ | x xs IH]; intros [ | n]; simpl; intros...
      - left; congruence.
      - enough (In x0 xs) by now right. eapply IH...
    Qed.

    Lemma lookup_Some (xs : list A) (i : nat)
      (RANGE : (i < length xs)%nat)
      : { x : A | xs !! i = Some x }.
    Proof.
      revert i RANGE; induction xs as [ | x xs IH].
      - simpl. intros; exfalso; word.
      - intros [ | i] ?; simpl in *.
        + exists x; trivial.
        + eapply IH; word.
    Qed.

  End MORE_LIST_LEMMAS.

  Class hsEq (A : Type) {well_formed : A -> Prop} : Type :=
    { eqProp (x : A) (y : A) : Prop
    ; eqb (x : A) (y : A) : bool 
    ; eqProp_reflexivity x
      (x_wf : well_formed x)
      : eqProp x x
    ; eqProp_symmetry x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      (x_eq_y : eqProp x y)
      : eqProp y x
    ; eqProp_transitivity x y z
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      (z_wf : well_formed z)
      (x_eq_y : eqProp x y)
      (y_eq_z : eqProp y z)
      : eqProp x z
    ; eqb_eq x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : eqb x y = true <-> eqProp x y
    ; eqb_neq x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : eqb x y = false <-> ~ eqProp x y
    }.

  #[global] Hint Resolve @eqProp_reflexivity @eqProp_symmetry @eqProp_transitivity : session_hints.
  #[global] Hint Rewrite @eqb_eq @eqb_neq : session_hints.

  Section hsEq_accessories.

    Context `{hsEq_A : hsEq A}.

    Lemma eqb_comm (x : A) (y : A)
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : eqb x y = eqb y x.
    Proof.
      destruct (eqb y x) as [ | ] eqn: H_OBS; [rewrite eqb_eq in H_OBS | rewrite eqb_neq in H_OBS]; trivial.
      - rewrite eqb_eq; eauto with *.
      - rewrite eqb_neq; eauto with *.
    Qed.

    Lemma eqb_obs (b : bool) (x : A) (y : A)
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : eqb x y = b <-> (if b then eqProp x y else ~ eqProp x y).
    Proof.
      destruct b; [eapply eqb_eq | eapply eqb_neq]; trivial.
    Qed.

  End hsEq_accessories.

  (** Section basic_instances_of_hsEq. *)

  #[global, program]
  Instance hsEq_preimage {A : Type} {B : Type}
    {well_formed : B -> Prop}
    {hsEq : SessionPrelude.hsEq B (well_formed := well_formed)}
    (f : A -> B)
    : SessionPrelude.hsEq A (well_formed := fun x : A => well_formed (f x)) :=
      { eqProp x y := eqProp (f x) (f y)
      ; eqb x y := eqb (f x) (f y)
      }.
  Next Obligation.
    simpl in *. eapply eqProp_reflexivity; trivial.
  Qed.
  Next Obligation.
    simpl in *. eapply eqProp_symmetry; trivial.
  Qed.
  Next Obligation.
    simpl in *. eapply eqProp_transitivity with (y := f y); trivial.
  Qed.
  Next Obligation.
    simpl. rewrite eqb_eq; trivial.
  Qed.
  Next Obligation.
    simpl. rewrite eqb_neq; trivial.
  Qed.

  #[global, program]
  Instance hsEq_nat : hsEq nat (well_formed := fun _ => True) :=
    { eqProp := @eq nat
    ; eqb := Nat.eqb
    ; eqProp_reflexivity := _
    ; eqProp_symmetry := _
    ; eqProp_transitivity := _
    ; eqb_eq x y _ _ := @Nat.eqb_eq x y
    ; eqb_neq x y _ _ := @Nat.eqb_neq x y
    }.
  Next Obligation.
    reflexivity; eauto.
  Qed.
  Next Obligation.
    symmetry; eauto.
  Qed.
  Next Obligation.
    etransitivity; eauto.
  Qed.

  #[global, program]
  Instance hsEq_Z : hsEq Z (well_formed := fun _ => True) :=
    { eqProp := @eq Z
    ; eqb := Z.eqb
    ; eqProp_reflexivity := _
    ; eqProp_symmetry := _
    ; eqProp_transitivity := _
    ; eqb_eq x y _ _ := @Z.eqb_eq x y
    ; eqb_neq x y _ _ := Z.eqb_neq x y
    }.
  Next Obligation.
    reflexivity; eauto.
  Qed.
  Next Obligation.
    symmetry; eauto.
  Qed.
  Next Obligation.
    etransitivity; eauto.
  Qed.

  #[global, program]
  Instance hsEq_u64 : hsEq u64 (well_formed := fun _ => True) :=
    { eqProp := @eq u64
    ; eqb x y := (uint.Z x =? uint.Z y)%Z
    ; eqProp_reflexivity := _
    ; eqProp_symmetry := _
    ; eqProp_transitivity := _
    ; eqb_eq := _
    ; eqb_neq := _
    }.
  Next Obligation.
    reflexivity; eauto.
  Qed.
  Next Obligation.
    symmetry; eauto.
  Qed.
  Next Obligation.
    etransitivity; eauto.
  Qed.
  Next Obligation.
    simpl. rewrite Z.eqb_eq. split.
    - intros EQ. word.
    - congruence.
  Qed.
  Next Obligation.
    simpl. rewrite Z.eqb_neq. split.
    - congruence.
    - intros NE. word.
  Qed.

  (** End basic_instances_of_hsEq. *)

  Class hsOrd (A : Type) {well_formed : A -> Prop} {hsEq : hsEq A (well_formed := well_formed)} : Type :=
    { ltProp (x : A) (y : A) : Prop
    ; ltb (x : A) (y : A) : bool
    ; ltProp_irreflexivity x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      (x_eq_y : eqProp x y)
      : ~ ltProp x y
    ; ltProp_transitivity x y z
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      (z_wf : well_formed z)
      (x_lt_y : ltProp x y)
      (y_lt_z : ltProp y z)
      : ltProp x z
    ; ltProp_trichotomy x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : ltProp x y \/ eqProp x y \/ ltProp y x
    ; ltb_lt x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : ltb x y = true <-> ltProp x y
    ; ltb_nlt x y
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : ltb x y = false <-> ~ ltProp x y
    }.

  #[global] Hint Resolve @ltProp_irreflexivity @ltProp_transitivity : session_hints.
  #[global] Hint Rewrite @ltb_lt @ltb_nlt : session_hints.

  Section hsOrd_accessories.

    Context `{hsOrd_A : hsOrd A}.

    Lemma ltb_ge (x : A) (y : A)
      (x_wf : well_formed x)
      (y_wf : well_formed y)
      : ltb x y = (negb (ltb y x) && negb (eqb x y))%bool.
    Proof.
      (destruct (ltb x y) as [ | ] eqn: H_OBS0; [rewrite ltb_lt in H_OBS0 | rewrite ltb_nlt in H_OBS0]);
      (destruct (ltb y x) as [ | ] eqn: H_OBS1; [rewrite ltb_lt in H_OBS1 | rewrite ltb_nlt in H_OBS1]);
      (destruct (eqb x y) as [ | ] eqn: H_OBS2; [rewrite eqb_eq in H_OBS2 | rewrite eqb_neq in H_OBS2]);
      simpl in *; try congruence.
      - contradiction (ltProp_irreflexivity x y); try done.
      - contradiction (ltProp_irreflexivity y y).
        + eapply eqProp_reflexivity; try done.
        + eapply ltProp_transitivity with (y := x); try done.
      - contradiction (ltProp_irreflexivity x y); try done.
      - pose proof (ltProp_trichotomy x y); tauto.
    Qed.

  End hsOrd_accessories.

  (** Section basic_instances_of_hsOrd. *)

  #[global, program]
  Instance hsOrd_preimage {A : Type} {B : Type}
    {well_formed : B -> Prop}
    {hsEq : SessionPrelude.hsEq B (well_formed := well_formed)}
    {hsOrd : SessionPrelude.hsOrd B (hsEq := hsEq)}
    (f : A -> B)
    : SessionPrelude.hsOrd A (hsEq := hsEq_preimage f):=
      { ltProp x y := ltProp (f x) (f y)
      ; ltb x y := ltb (f x) (f y)
      }.
  Next Obligation.
    eapply (ltProp_irreflexivity (f x) (f y)); trivial.
  Qed.
  Next Obligation.
    eapply (ltProp_transitivity (f x) (f y) (f z)); trivial.
  Qed.
  Next Obligation.
    eapply (ltProp_trichotomy (f x) (f y)); trivial.
  Qed.
  Next Obligation.
    simpl. rewrite ltb_lt; trivial.
  Qed.
  Next Obligation.
    simpl. rewrite ltb_nlt; trivial.
  Qed.

  #[global, program]
  Instance hsOrd_nat : hsOrd nat :=
    { ltProp x y := (x < y)%nat
    ; ltb := Nat.ltb
    ; ltProp_irreflexivity := _
    ; ltProp_transitivity := _
    ; ltProp_trichotomy := _
    ; ltb_lt x y := _
    ; ltb_nlt x y := _
    }.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl. eapply Nat.ltb_lt.
  Qed.
  Next Obligation.
    simpl. rewrite Nat.ltb_ge. word.
  Qed.

  #[global, program]
  Instance hsOrd_Z : hsOrd Z :=
    { ltProp x y := (x < y)%Z
    ; ltb := Z.ltb
    ; ltProp_irreflexivity := _
    ; ltProp_transitivity := _
    ; ltProp_trichotomy := _
    ; ltb_lt x y := _
    ; ltb_nlt x y := _
    }.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl. rewrite Z.ltb_lt. word.
  Qed.
  Next Obligation.
    simpl. rewrite Z.ltb_ge. word.
  Qed.

  #[global, program]
  Instance hsOrd_u64 : hsOrd u64 :=
    { ltProp x y := (uint.Z x < uint.Z y)%Z
    ; ltb x y := (uint.Z y >? uint.Z x)%Z
    ; ltProp_irreflexivity := _
    ; ltProp_transitivity := _
    ; ltProp_trichotomy := _
    ; ltb_lt x y := _
    ; ltb_nlt x y := _
    }.
  Next Obligation.
    simpl. do 2 red in x_eq_y. word.
  Qed.
  Next Obligation.
    simpl in *. word.
  Qed.
  Next Obligation.
    simpl in *.
    assert (uint.Z x < uint.Z y \/ uint.Z x = uint.Z y \/ uint.Z x > uint.Z y) as [LT | [EQ | GT]] by word.
    - left. word.
    - right. left. word. 
    - right. right. word.
  Qed.
  Next Obligation.
    rewrite Z.gtb_gt. word.
  Qed.
  Next Obligation.
    simpl. rewrite Z.gtb_ltb Z.ltb_ge. word.
  Qed.

  (** End basic_instances_of_hsOrd. *)

  Section SORTED.

    Context {A : Type} {well_formed : A -> Prop}.

    Lemma Forall_well_formed_elim (xs : list A)
      (xs_wf : Forall well_formed xs)
      : ∀ x : A, ∀ i : nat, xs !! i = Some x -> well_formed x.
    Proof.
      induction xs_wf as [ | x xs x_wf xs_wf IH]; intros x0 i H_x0.
      - rewrite lookup_nil in H_x0. congruence.
      - rewrite lookup_cons in H_x0. destruct i as [ | i'].
        + congruence.
        + eapply IH with (i := i'); trivial.
    Qed.

    #[local] Hint Resolve Forall_well_formed_elim : core.

    Context {hsEq : hsEq A (well_formed := well_formed)}.

    Context {hsOrd : hsOrd A (hsEq := hsEq)}.

    Definition isSorted (xs : list A) : Prop :=
      ∀ i : nat, ∀ j : nat, (i < j)%nat ->
      ∀ x1 : A, ∀ x2 : A, xs !! i = Some x1 -> xs !! j = Some x2 -> ltb x1 x2 = true.

    Lemma isSorted_middle_1 (xs : list A) (y : A) (zs : list A)
      (SORTED : isSorted (xs ++ y :: zs))
      : isSorted (xs ++ zs).
    Proof.
      intros i j i_lt_j x1 x2 H_x1 H_x2.
      assert (i < length xs \/ i >= length xs)%nat as [H_i | H_i] by word; assert (j < length xs \/ j >= length xs)%nat as [H_j | H_j] by word.
      - rewrite lookup_app_l in H_x1; trivial. rewrite lookup_app_l in H_x2; trivial. eapply SORTED with (i := i) (j := j).
        + word.
        + rewrite lookup_app_l; trivial.
        + rewrite lookup_app_l; trivial.
      - rewrite lookup_app_l in H_x1; trivial. rewrite lookup_app_r in H_x2; trivial. eapply SORTED with (i := i) (j := (j + 1)%nat).
        + word.
        + rewrite lookup_app_l; trivial.
        + replace (j + 1)%nat with (S j) by word. rewrite lookup_app_r.
          * rewrite lookup_cons. replace (S j - length xs)%nat with (S (j - length xs)%nat); trivial. word.
          * word.
      - word.
      - rewrite lookup_app_r in H_x1; trivial. rewrite lookup_app_r in H_x2; trivial. eapply SORTED with (i := (i + 1)%nat) (j := (j + 1)%nat).
        + word.
        + replace (i + 1)%nat with (S i) by word. rewrite lookup_app_r.
          * rewrite lookup_cons. replace (S i - length xs)%nat with (S (i - length xs)%nat); trivial. word.
          * word.
        + replace (j + 1)%nat with (S j) by word. rewrite lookup_app_r.
          * rewrite lookup_cons. replace (S j - length xs)%nat with (S (j - length xs)%nat); trivial. word.
          * word.
    Qed.

    Lemma isSorted_middle (xs : list A) (ys : list A) (zs : list A)
      (SORTED : isSorted (xs ++ ys ++ zs))
      : isSorted (xs ++ zs).
    Proof.
      revert xs zs SORTED; induction ys as [ | y ys IH]; intros; simpl in *; trivial.
      eapply IH. eapply isSorted_middle_1. exact SORTED.
    Qed.

    Lemma isSorted_NoDup l (l_wf : Forall well_formed l)
      (SORTED : isSorted l)
      : NoDup l.
    Proof with eauto.
      induction l_wf as [ | x xs x_wf xs_wf IH]; simpl; econstructor.
      - intros H_contra. clear IH. induction H_contra; simpl in *.
        + contradiction (ltProp_irreflexivity x x)...
          * eapply eqProp_reflexivity...
          * rewrite <- ltb_lt... eapply SORTED with (i := 0%nat) (j := 1%nat)...
        + inv xs_wf. enough (isSorted (x :: l))...
          replace (x :: l) with ([x] ++ l)... replace (x :: y :: l) with ([x] ++ [y] ++ l) in SORTED...
          eapply isSorted_middle...
      - eapply IH. replace xs with ([] ++ xs)... replace (x :: xs) with ([] ++ [x] ++ xs) in SORTED...
        eapply isSorted_middle...
    Qed.

    Fixpoint sortedInsert (l : list A) (i : A) : list A :=
      match l with
      | [] => [i]
      | h :: t =>
        if ltb i h then
          i :: h :: t
        else if eqb h i then
          h :: t
        else
          h :: sortedInsert t i
      end.

    Lemma sortedInsert_spec (l : list A) (i : A) (l_wf : Forall well_formed l) (i_wf : well_formed i)
      (SORTED : isSorted l)
      (NOT_IN := forallb (fun j => negb (eqb j i)) l)
      : ∃ prefix, ∃ suffix, l = prefix ++ suffix /\
        sortedInsert l i = prefix ++ (if NOT_IN then [i] else []) ++ suffix /\
        (∀ n : nat, ∀ x : A, prefix !! n = Some x -> ltb x i = true) /\
        (∀ n : nat, ∀ x : A, suffix !! n = Some x -> if NOT_IN then ltb i x = true else ltb i x = true \/ eqb i x = true) /\
        Forall well_formed (sortedInsert l i).
    Proof with eauto.
      remember l as l' eqn: H_l' in NOT_IN. subst NOT_IN. destruct (forallb (λ j : A, negb (hsEq .(eqb) j i)) l') as [ | ] eqn: H_In.
      - assert (SUBLIST : forall x, In x l -> In x l') by now subst l'.
        rewrite forallb_spec in H_In. clear H_l'; revert i SORTED i_wf l' SUBLIST H_In.
        induction l_wf as [ | x1 xs x1_wf xs_wf IH]; intros x0 SORTED' x0_wf l SUBLIST NOT_In; simpl in *.
        + exists []. exists []. simpl. split. { done. } split. { reflexivity. } split.
          { intros n x H_x. rewrite lookup_nil in H_x. congruence. } split.
          { intros n x H_x. rewrite lookup_nil in H_x. congruence. } econstructor...
        + assert (SORTED : isSorted xs).
          { intros i j i_lt_j x x' H_x H_x'. eapply SORTED' with (i := S i) (j := S j); try (word || done). }
          assert (SUBLIST' : forall x, In x xs -> In x l) by now firstorder.
          assert (NOT_In' : forall x, In x l -> negb (eqb x x0) = true) by now firstorder.
          specialize (IH x0 SORTED x0_wf l SUBLIST' NOT_In').
          destruct IH as (prefix & suffix & -> & EQ & H_prefix & H_suffix & H_wf)... simpl.
          destruct (ltb x0 x1) as [ | ] eqn: H_OBS; [rewrite ltb_lt in H_OBS | rewrite ltb_nlt in H_OBS]...
          { exists []. exists (x1 :: prefix ++ suffix)%list.
            enough (WTS : forall n : nat, forall x, (x1 :: prefix ++ suffix) !! n = Some x -> ltb x0 x = true).
            { repeat (split; try done). econstructor... }
            intros n x H_x. assert (n = 0 \/ 0 < n)%nat as [-> | LT] by word.
            - simpl in H_x. assert (x = x1) as -> by congruence. rewrite ltb_lt...
            - rewrite -> ltb_lt... eapply ltProp_transitivity with (y := x1)... rewrite <- ltb_lt...
          }
          destruct (eqb x1 x0) as [ | ] eqn: H_OBS'; rewrite eqb_obs in H_OBS'...
          { pose proof (NOT_In x1 (SUBLIST x1 (or_introl eq_refl))) as claim1. rewrite negb_true_iff in claim1. rewrite eqb_neq in claim1... contradiction. }
          { exists (x1 :: prefix)%list. exists suffix. split. { done. } split. { simpl. rewrite EQ. simpl. reflexivity. }
            assert (WTS : forall n : nat, forall x, suffix !! n = Some x -> ltb x0 x = true) by done.
            repeat (split; try done)... intros [ | n]; simpl; intros x H_x...
            assert (x = x1) as -> by congruence. clear H_x.
            rewrite ltb_lt... pose proof (ltProp_trichotomy x0 x1) as [? | [? | ?]]; try done...
            contradiction H_OBS'. eapply eqProp_symmetry...
          }
      - subst l'. rewrite forallb_spec in H_In. destruct H_In as (x2 & x2_in & EQ). rewrite negb_false_iff in EQ.
        assert (x2_wf : well_formed x2).
        { eapply List.Forall_forall... }
        rewrite eqb_eq in EQ... simpl; revert SORTED i i_wf x2 x2_in x2_wf EQ.
        induction l_wf as [ | x1 xs x1_wf xs_wf IH]; simpl; intros SORTED' x0 x0_wf x2 x2_in x2_wf EQ.
        { tauto. }
        assert (SORTED : isSorted xs).
        { intros i j i_lt_j x x' H_x H_x'. eapply SORTED' with (i := S i) (j := S j); try (word || done). }
        destruct x2_in as [<- | x2_in].
        + replace (eqb x1 x0) with true by now symmetry; eapply eqb_eq; trivial.
          replace (ltb x0 x1) with false; cycle 1.
          { symmetry. rewrite ltb_nlt... intros H_contra. eapply (ltProp_irreflexivity x0 x1)... eapply eqProp_symmetry... }
          exists []. exists (x1 :: xs). simpl. repeat (split; try done)...
          intros [ | n]; simpl; intros x H_x.
          * assert (x = x1) as -> by congruence. clear H_x.
            rewrite ltb_lt... rewrite eqb_eq... pose proof (ltProp_trichotomy x0 x1) as [? | [? | ?]]; try done...
            contradiction (ltProp_irreflexivity x1 x0)...
          * assert (claim1 : ltb x1 x = true).
            { eapply SORTED' with (i := 0%nat) (j := S n); try (word || done). }
            rewrite ltb_lt in claim1... rewrite ltb_lt... rewrite eqb_eq...
            pose proof (ltProp_trichotomy x0 x) as [? | [? | ?]]...
            contradiction (ltProp_irreflexivity x1 x0)... eapply ltProp_transitivity with (y := x)...
        + destruct (ltb x0 x1) as [ | ] eqn: H_OBS1; [rewrite ltb_lt in H_OBS1 | rewrite ltb_nlt in H_OBS1]...
          { contradiction (ltProp_irreflexivity x0 x2)...
            - eapply eqProp_symmetry...
            - pose proof (In_lookup xs x2 x2_in) as (n & H_OBS & LEN).
              eapply ltProp_transitivity with (y := x1)... rewrite <- ltb_lt... eapply SORTED' with (i := 0%nat) (j := S n)... word.
          }
          destruct (eqb x1 x0) as [ | ] eqn: H_OBS2; [rewrite eqb_eq in H_OBS2 | rewrite eqb_neq in H_OBS2]...
          { exists []. exists (x1 :: xs). simpl. repeat (split; try done)...
            intros [ | n]; simpl; intros x H_x.
            - assert (x = x1) as -> by congruence. clear H_x.
              rewrite ltb_lt... rewrite eqb_eq... pose proof (ltProp_trichotomy x0 x1) as [? | [? | ?]]; try done...
              contradiction (ltProp_irreflexivity x1 x0)...
            - assert (claim1 : ltb x1 x = true).
              { eapply SORTED' with (i := 0%nat) (j := S n); try (word || done). }
              rewrite ltb_lt in claim1... rewrite ltb_lt... rewrite eqb_eq...
              pose proof (ltProp_trichotomy x0 x) as [? | [? | ?]]...
              contradiction (ltProp_irreflexivity x1 x0)... eapply ltProp_transitivity with (y := x)...
          }
          { pose proof (IH SORTED x0 x0_wf x2 x2_in x2_wf EQ) as (prefix & suffix & -> & IH' & H_prefix & H_suffix & WF).
            exists (x1 :: prefix). exists suffix. simpl. rewrite IH'. repeat (split; try done)...
            intros [ | n]; simpl; intros x H_x...
            assert (x = x1) as -> by congruence. clear H_x.
            rewrite ltb_lt... pose proof (ltProp_trichotomy x1 x0) as [? | [? | ?]]...
            - contradiction H_OBS2.
            - contradiction H_OBS1.
          }
    Qed.

    Lemma sortedInsert_isSorted l i (l_wf : Forall well_formed l) (i_wf : well_formed i)
      (SORTED : isSorted l)
      : isSorted (sortedInsert l i).
    Proof with try (word || congruence || eauto || done).
      pose proof (sortedInsert_spec l i l_wf i_wf SORTED) as (prefix & suffix & H_l & -> & H_prefix & H_suffix & H_wf).
      rename i into x, l into xs. intros i j LE x1 x2 H_x1 H_x2.
      destruct (forallb (fun j : A => negb (eqb j x)) xs) as [ | ] eqn: H_OBS; simpl.
      { assert (i < length prefix \/ i = length prefix \/ i > length prefix)%nat as [i_lt | [i_eq | i_gt]] by word;
        assert (j < length prefix \/ j = length prefix \/ j > length prefix)%nat as [j_lt | [j_eq | j_gt]] by word.
        - eapply SORTED with (i := i) (j := j)...
          + rewrite H_l. rewrite lookup_app_l... rewrite lookup_app_l in H_x1...
          + rewrite H_l. rewrite lookup_app_l... rewrite lookup_app_l in H_x2...
        - rewrite list_lookup_middle in H_x2...
          assert (x = x2) as -> by congruence. clear H_x2.
          eapply H_prefix. rewrite lookup_app_l in H_x1...
        - rewrite ltb_lt... eapply ltProp_transitivity with (y := x)...
          + rewrite <- ltb_lt... eapply H_prefix with (n := i)... rewrite lookup_app_l in H_x1...
          + rewrite <- ltb_lt... eapply H_suffix with (n := (j - (length prefix + 1))%nat)... rewrite lookup_app_r in H_x2... rewrite lookup_app_r in H_x2; simpl in *...
            replace (j - (length prefix + 1))%nat with (j - length prefix - 1)%nat by word...
        - rewrite list_lookup_middle in H_x1...
        - word.
        - rewrite list_lookup_middle in H_x1...
          assert (x = x1) as -> by congruence. clear H_x1. eapply H_suffix. rewrite app_assoc in H_x2. rewrite lookup_app_r in H_x2...
          rewrite length_app. simpl. word.
        - word.
        - word.
        - eapply SORTED with (i := (i - 1)%nat) (j := (j - 1)%nat)...
          + rewrite H_l. rewrite lookup_app_r... rewrite app_assoc in H_x1. rewrite lookup_app_r in H_x1; simpl in *.
            * rewrite length_app in H_x1. simpl in *. replace (i - 1 - length prefix)%nat with (i - (length prefix + 1))%nat by word...
            * rewrite length_app. simpl...
          + rewrite H_l. rewrite lookup_app_r... rewrite app_assoc in H_x2. rewrite lookup_app_r in H_x2; simpl in *.
            * rewrite length_app in H_x2. simpl in *. replace (j - 1 - length prefix)%nat with (j - (length prefix + 1))%nat by word...
            * rewrite length_app. simpl...
      }
      { simpl in *; subst xs... }
    Qed.

    Inductive binarySearchLoop_spec (needle : A) (xs : list A) (i : nat) (j : nat) : nat -> Prop :=
      | binarySearchLoop_spec_break
        (BREAK : (i >= j)%nat)
        : binarySearchLoop_spec needle xs i j i
      | binarySearchLoop_spec_conti res x
        (CONTINUE : (i < j)%nat)
        (mid := (i + (j - i) `div` 2)%nat)
        (LOOKUP : xs !! mid = Some x)
        (i' := if ltb x needle then (mid + 1)%nat else i)
        (j' := if ltb x needle then j else mid)
        (LOOP : binarySearchLoop_spec needle xs i' j' res)
        : binarySearchLoop_spec needle xs i j res.

    Lemma binarySearchLoop_exists_uniquely (needle : A) (xs : list A) (i : nat) (j : nat) (i_BOUND : (i <= j)%nat) (j_BOUND : (j <= length xs)%nat)
      : { res : nat | binarySearchLoop_spec needle xs i j res /\ (forall res', binarySearchLoop_spec needle xs i j res' -> res = res') }.
    Proof.
      remember (j - i)%nat as l eqn: H_l. assert (j = l + i)%nat as -> by word. clear H_l i_BOUND. revert i j_BOUND. induction (lt_wf l) as [l _ IH]. intros. set (l + i)%nat as j in *.
      assert ({ i >= j } + { i < j })%nat as [GE | LT].
      { subst j. generalize (l + i)%nat as j. clear. induction i as [ | i IH], j as [ | j]; simpl; try first [left; word | right; word]. specialize IH with (j := j). destruct IH as [IH | IH]; [left | right]; word. }
      - exists i. split.
        { econstructor 1; trivial. }
        { intros res' H_res'. inversion H_res'; try word. }
      - set (i + (j - i) `div` 2)%nat as mid.
        assert (mid < length xs)%nat as H_mid.
        { enough (mid < j)%nat by word. pose proof (Nat.div_mod (j - i)%nat 2%nat). pose proof (Nat.mod_bound_pos (j - i)%nat 2%nat). word. }
        pose proof (lookup_Some xs mid H_mid) as [x H_x].
        set (i' := if ltb x needle then (mid + 1)%nat else i). set (j' := if ltb x needle then j else mid).
        assert ((j' - i') < l)%nat as MEASURE.
        { destruct (ltb x needle) as [ | ]; subst i' j' j mid; try word. replace (l + i - i)%nat with l in * by word. pose proof (Nat.div_mod l 2%nat). pose proof (Nat.mod_bound_pos l 2%nat). word. }
        assert (j' - i' + i' <= length xs)%nat as BOUND.
        { subst i' j'. destruct (ltb x needle) as [ | ]; word. }
        pose proof (IH (j' - i')%nat MEASURE i' BOUND) as [res [H_res UNIQUE]].
        assert (j' = j' - i' + i')%nat as MOTTO.
        { enough (i' <= j') by word. destruct (ltb x needle) as [ | ]; try word. subst i' j'. pose proof (Nat.div_mod (j - i)%nat 2%nat). pose proof (Nat.mod_bound_pos (j - i)%nat 2%nat). word. }
        exists res. replace (j' - i' + i')%nat with j' in H_res. split; [econstructor 2; eauto | intros res' H_res'; eapply UNIQUE; rewrite <- MOTTO; inversion H_res'; subst; [word | ]].
        enough (i' = i'0 /\ j' = j'0) as [? ?] by congruence. assert (mid = mid0) as H_mid1 by word. assert (x0 = x) as <- by congruence. destruct (ltb x0 needle); split; try word.
    Qed.

    Definition binarySearchLoop (needle : A) (xs : list A) (i : nat) (j : nat) (i_BOUND : (i <= j)%nat) (j_BOUND : (j <= length xs)%nat) : nat :=
      proj1_sig (binarySearchLoop_exists_uniquely needle xs i j i_BOUND j_BOUND).

    Lemma binarySearchLoop_break (needle : A) (xs : list A) (i : nat) (j : nat) (i_BOUND : (i <= j)%nat) (j_BOUND : (j <= length xs)%nat)
      (BREAK : (i >= j)%nat)
      : binarySearchLoop needle xs i j i_BOUND j_BOUND = i.
    Proof.
      unfold binarySearchLoop. destruct (binarySearchLoop_exists_uniquely needle xs i j i_BOUND j_BOUND) as [res [H_res UNIQUE]]; simpl.
      eapply UNIQUE. econstructor 1; trivial.
    Qed.

    Lemma binarySearchLoop_continue (needle : A) (xs : list A) (i : nat) (j : nat) (i_BOUND : (i <= j)%nat) (j_BOUND : (j <= length xs)%nat) (x : A)
      (CONTINUE : (i < j)%nat)
      (mid := (i + (j - i) `div` 2)%nat)
      (LOOKUP : xs !! mid = Some x)
      (i' := if ltb x needle then (mid + 1)%nat else i)
      (j' := if ltb x needle then j else mid)
      : { STEP : (i' <= j' /\ j' <= length xs)%nat | binarySearchLoop needle xs i j i_BOUND j_BOUND = binarySearchLoop needle xs i' j' (proj1 STEP) (proj2 STEP) }.
    Proof.
      unfold binarySearchLoop. destruct (binarySearchLoop_exists_uniquely needle xs i j i_BOUND j_BOUND) as [res [H_res UNIQUE]]; simpl.
      assert (i' <= j')%nat as H_i'. { destruct (ltb x needle) as [ | ]; try word. pose proof (Nat.div_mod (j - i)%nat 2%nat). pose proof (Nat.mod_bound_pos (j - i)%nat 2%nat). word. }
      assert (j' <= length xs)%nat as H_j'. { destruct (ltb x needle) as [ | ]; try word. pose proof (Nat.div_mod (j - i)%nat 2%nat). pose proof (Nat.mod_bound_pos (j - i)%nat 2%nat). word. }
      exists (conj H_i' H_j'). eapply UNIQUE. econstructor 2; eauto. fold mid. fold i'. fold j'.
      destruct (binarySearchLoop_exists_uniquely needle xs i' j' (proj1 (conj H_i' H_j')) (proj2 (conj H_i' H_j'))) as [res' [H_res' UNIQUE']]; trivial.
    Qed.

    Definition binarySearchLoop' (needle : A) (xs : list A) (i : nat) (j : nat) : option nat :=
      match le_gt_dec i j, le_gt_dec j (length xs) with
      | left i_BOUND, left j_BOUND => Some (binarySearchLoop needle xs i j i_BOUND j_BOUND)
      | _, _ => None
      end.

    #[local] Opaque Nat.div.

    Lemma unfold_binarySearchLoop' (needle : A) (xs : list A) (i : nat) (j : nat) :
      binarySearchLoop' needle xs i j =
      match le_gt_dec i j, le_gt_dec j (length xs) with
      | left _, left _ =>
        if ltb i j
        then
          let mid := (i + (j - i) `div` 2)%nat in
          match xs !! mid with
          | Some x =>
            let i' := if ltb x needle then (mid + 1)%nat else i in
            let j' := if ltb x needle then j else mid in
            binarySearchLoop' needle xs i' j'
          | None => None
          end
        else Some i
      | _, _ => None
      end.
    Proof.
      unfold binarySearchLoop' at 1. destruct (le_gt_dec i j) as [i_BOUND | i_BOUND], (le_gt_dec j (length xs)) as [j_BOUND | j_BOUND]; trivial.
      destruct (ltb i j) as [ | ] eqn: H_OBS.
      - rewrite ltb_lt in H_OBS; trivial. do 2 red in H_OBS.
        assert (i + (j - i) `div` 2 < length xs)%nat as BOUND.
        { pose proof (Nat.div_mod (j - i)%nat 2%nat). pose proof (Nat.mod_bound_pos (j - i)%nat 2%nat). word. }
        pose proof (lookup_Some _ _ BOUND) as [x H_x]. rewrite H_x.
        pose proof (binarySearchLoop_continue needle xs i j i_BOUND j_BOUND x H_OBS) as claim. simpl in claim. specialize (claim H_x).
        destruct claim as [[YES1 YES2] EQ]. rewrite EQ. unfold binarySearchLoop'. simpl.
        set (if hsOrd .(ltb) x needle then (i + (j - i) `div` 2 + 1)%nat else i)%nat as i'.
        set (if hsOrd .(ltb) x needle then j else (i + (j - i) `div` 2)%nat)%nat as j'.
        destruct (le_gt_dec i' j') as [LE' | GT'], (le_gt_dec j' (length xs)) as [LE'' | GT'']; try word.
        f_equal. f_equal; eapply le_proof_irrel.
      - rewrite ltb_nlt in H_OBS; trivial. simpl ltProp in H_OBS. f_equal. eapply binarySearchLoop_break. word.
    Qed.

    Definition binarySearch (needle : A) (xs : list A) : nat :=
      binarySearchLoop needle xs 0%nat (length xs) nat_le_0_n nat_le_n_n.

  End SORTED.

  Section VECTOR.

    #[local] Open Scope list_scope.

    #[local] Notation "x =? y" := (SessionPrelude.eqb x y).

    #[local] Notation "x >? y" := (SessionPrelude.ltb y x).

    Context {A : Type} {well_formed : A -> Prop}.

    #[local] Hint Resolve ( @Forall_well_formed_elim A well_formed) : core.

    Context {hsEq : hsEq A (well_formed := well_formed)}.

    Fixpoint vectorEq (v1 : list A) (v2 : list A) : bool :=
      match v1 with
      | [] => true
      | h1 :: t1 =>
        match v2 with
        | [] => true
        | h2 :: t2 => if negb (h1 =? h2) then false else vectorEq t1 t2
        end
      end.

    #[global, program]
    Instance hsEq_vector (len : nat) : SessionPrelude.hsEq (list A) (well_formed := fun l => Forall well_formed l /\ length l = len) :=
      { eqProp xs1 xs2 := ∀ i : nat, (i < len)%nat -> ∀ x1 : A, ∀ x2 : A, xs1 !! i = Some x1 -> xs2 !! i = Some x2 -> eqb x1 x2 = true
      ; eqb := vectorEq
      ; eqProp_reflexivity xs1 xs1_wf := _
      ; eqProp_symmetry xs1 xs2 xs1_wf xs2_wf xs1_eq_xs2 := _
      ; eqProp_transitivity xs1 xs2 xs3 xs1_wf xs2_wf xs3_wf xs1_eq_xs2 xs2_eq_xs3 := _
      }.
    Next Obligation with eauto 2.
      destruct xs1_wf as [xs1_wf xs1_len].
      intros i i_bound x1 x2 H_x1 H_x2; simpl in *.
      replace x1 with x2 by congruence.
      rewrite eqb_eq... eapply eqProp_reflexivity...
    Qed.
    Next Obligation with eauto 2.
      destruct xs1_wf as [xs1_wf xs1_len], xs2_wf as [xs2_wf xs2_len].
      intros i i_bound x1 x2 H_x1 H_x2; simpl in *.
      rewrite eqb_comm...
    Qed.
    Next Obligation with eauto 2.
      destruct xs1_wf as [xs1_wf xs1_len], xs2_wf as [xs2_wf xs2_len], xs3_wf as [xs3_wf xs3_len].
      intros i i_bound x1 x2 H_x1 H_x2; simpl in *.
      rewrite <- xs2_len in i_bound.
      pose proof (list_lookup_lt xs2 i i_bound) as (x3 & H_x3).
      rewrite eqb_eq... eapply eqProp_transitivity with (y := x3)...
      - rewrite <- eqb_eq... eapply xs1_eq_xs2 with (i := i)... rewrite <- xs2_len...
      - rewrite <- eqb_eq... eapply xs2_eq_xs3 with (i := i)... rewrite <- xs2_len...
    Qed.
    Next Obligation with eauto 2.
      destruct x_wf as [x_wf x_len], y_wf as [y_wf y_len]. simpl in *. split.
      - revert len x_len y y_len y_wf. induction x_wf as [ | hx tx hx_wf tx_wf IH]; intros ? <- [ | hy ty] LEN_EQ y_wf EQ [ | i'] i_bound x1 x2 H_x1 H_x2; simpl in *; try congruence; try word; inv y_wf.
        + rewrite eqb_eq... destruct (x1 =? x2) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS... all: simpl in *; congruence.
        + rewrite eqb_eq... destruct (hx =? hy) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS... all: simpl in *; try congruence.
          rewrite <- eqb_eq... eapply IH with (y := ty) (i := i')... all: try word || done.
      - revert len x_len y y_len y_wf. induction x_wf as [ | hx tx hx_wf tx_wf IH]; intros ? <- [ | hy ty] LEN_EQ y_wf EQ; simpl in *; try congruence; try word; inv y_wf.
        destruct (hx =? hy) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS; simpl in *...
        + eapply IH... all: try (word || done). intros i i_bound x1 x2 H_x1 H_x2.
          eapply EQ with (i := S i)... word.
        + contradiction H_OBS. rewrite <- eqb_eq... eapply EQ with (i := 0%nat)... word.
    Qed.
    Next Obligation with eauto 2.
      destruct x_wf as [x_wf x_len], y_wf as [y_wf y_len]. simpl in *. split.
      - revert len x_len y y_len y_wf. induction x_wf as [ | hx tx hx_wf tx_wf IH]; intros ? <- [ | hy ty] LEN_EQ y_wf NE H_contra; simpl in *; try congruence; try word; inv y_wf.
        destruct (hx =? hy) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS; simpl in *...
        + eapply IH with (y := ty)... all: try (word || done). intros i i_bound x1 x2 H_x1 H_x2.
          eapply H_contra with (i := S i)... word.
        + contradiction H_OBS. rewrite <- eqb_eq... eapply H_contra with (i := 0%nat)... word.
      - revert len x_len y y_len y_wf. induction x_wf as [ | hx tx hx_wf tx_wf IH]; intros ? <- [ | hy ty] LEN_EQ y_wf NE; simpl in *; try congruence; try word; inv y_wf.
        + contradiction NE. word.
        + destruct (hx =? hy) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS; simpl in *...
          eapply IH with (y := ty)... all: try (word || done). intros H_contra. contradiction NE.
          intros [ | i'] i_bound x1 x2 H_x1 H_x2; simpl in *...
          * rewrite eqb_eq... all: try congruence.
          * eapply H_contra with (i := i')... word.
    Qed.

    Context {hsOrd : hsOrd A (hsEq := hsEq)}.

    Fixpoint vectorGt (v1 : list A) (v2 : list A) : bool :=
      match v1 with
      | [] => false 
      | h1 :: t1 =>
        match v2 with
        | [] => false 
        | h2 :: t2 => if h1 =? h2 then vectorGt t1 t2 else h1 >? h2
        end
      end.

    Lemma vectorGt_transitive l1 l2 l3 (l1_wf : Forall well_formed l1) (l2_wf : Forall well_formed l2) (l3_wf : Forall well_formed l3) :
      vectorGt l3 l2 = true ->
      vectorGt l2 l1 = true ->
      vectorGt l3 l1 = true.
    Proof with congruence || trivial || eauto 2.
      revert l1 l3 l1_wf l3_wf; induction l2_wf as [ | x2 l2 x2_wf l2_wf IH]; intros ? ? [ | x1 l1 x1_wf l1_wf] [ | x3 l3 x3_wf l3_wf]; simpl in *...
      repeat (
        let H_OBS := fresh "H_OBS" in
        lazymatch goal with
        | [ |- context [ (eqb _ _) ] ] => destruct (eqb _ _) as [ | ] eqn: H_OBS; [rewrite eqb_eq in H_OBS | rewrite eqb_neq in H_OBS]; trivial
        | [ |- context [ (ltb _ _) ] ] => destruct (ltb _ _) as [ | ] eqn: H_OBS; [rewrite ltb_lt in H_OBS | rewrite ltb_nlt in H_OBS]; trivial
        end
      ); intros l3_gt_l2 l2_gt_l1...
      - contradiction H_OBS1. eapply eqProp_transitivity with (y := x2)...
      - contradiction H_OBS0. eapply eqProp_transitivity with (y := x3)... eapply eqProp_symmetry...
      - pose proof (ltProp_trichotomy x3 x1) as [? | [? | ?]]; try done.
        contradiction (ltProp_irreflexivity x3 x2)... eapply ltProp_transitivity with (y := x1)...
      - contradiction H_OBS. eapply eqProp_transitivity with (y := x1)... eapply eqProp_symmetry...
      - pose proof (ltProp_trichotomy x3 x1) as [? | [? | ?]]; try done.
        contradiction (ltProp_irreflexivity x2 x1)... eapply ltProp_transitivity with (y := x3)...
      - contradiction (ltProp_irreflexivity x1 x3); try done.
        + eapply eqProp_symmetry...
        + eapply ltProp_transitivity with (y := x2)...
      - contradiction H_OBS4. eapply ltProp_transitivity with (y := x2)...
    Qed.

    Lemma vectorGt_implies_not_vectorEq l1 l2 (l1_wf : Forall well_formed l1) (l2_wf : Forall well_formed l2) :
      vectorGt l1 l2 = true ->
      vectorEq l1 l2 = false.
    Proof.
      revert l2 l2_wf. induction l1_wf as [ | x1 xs1 x1_wf xs1_wf IH]; intros ? [ | x2 xs2 x2_wf xs2_wf]; simpl; intros EQ; try congruence.
      destruct (x1 =? x2) as [ | ] eqn: H_OBS; [rewrite eqb_eq in H_OBS | rewrite eqb_neq in H_OBS]; trivial; simpl in *.
      eapply IH; trivial.
    Qed.

    Lemma vectorEq_implies_not_vectorGt l1 l2 (l1_wf : Forall well_formed l1) (l2_wf : Forall well_formed l2) :
      vectorEq l1 l2 = true ->
      vectorGt l1 l2 = false.
    Proof.
      revert l2 l2_wf. induction l1_wf as [ | x1 xs1 x1_wf xs1_wf IH]; intros ? [ | x2 xs2 x2_wf xs2_wf]; simpl; intros EQ; try congruence.
      destruct (x1 =? x2) as [ | ] eqn: H_OBS; [rewrite eqb_eq in H_OBS | rewrite eqb_neq in H_OBS]; trivial; simpl in *.
      - eapply IH; trivial.
      - congruence.
    Qed.

    #[global, program]
    Instance hsOrd_vector (len : nat) : SessionPrelude.hsOrd (list A) (hsEq := hsEq_vector len) :=
      { ltProp xs1 xs2 := vectorGt xs2 xs1 = true
      ; ltb xs1 xs2 := vectorGt xs2 xs1
      }.
    Next Obligation with eauto 2.
      simpl in *. destruct x_wf as [x_wf x_len], y_wf as [y_wf y_len].
      rewrite vectorEq_implies_not_vectorGt...
      change vectorEq with ( @eqb (list A) _ (hsEq_vector len)).
      rewrite eqb_comm... rewrite eqb_eq...
    Qed.
    Next Obligation with eauto 2.
      simpl in *. destruct x_wf as [x_wf x_len], y_wf as [y_wf y_len], z_wf as [z_wf z_len].
      simpl in *. eapply vectorGt_transitive with (l2 := y)...
    Qed.
    Next Obligation with eauto 2.
      simpl in *. destruct x_wf as [x_wf x_len], y_wf as [y_wf y_len]. revert y y_wf y_len. revert len x_len.
      induction x_wf as [ | hx tx hx_wf tx_wf IH]; intros ? <- ? [ | hy ty hy_wf ty_wf] LEN_EQ; simpl in *; try congruence...
      - right. left. word.
      - destruct (hx =? hy) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS; simpl in *...
        + apply eqProp_symmetry in H_OBS... rewrite <- eqb_eq in H_OBS... rewrite H_OBS. symmetry in LEN_EQ.
          specialize (IH (length ty) (f_equal Nat.pred LEN_EQ) ty ty_wf eq_refl). destruct IH as [IH | [IH | IH]]; try tauto.
          right. left. intros [ | i'] i_bound x1 x2 H_x1 H_x2; simpl in *.
          * rewrite eqb_comm in H_OBS... congruence.
          * eapply IH with (i := i')... word.
        + rewrite <- eqb_neq in H_OBS... rewrite eqb_comm in H_OBS... rewrite H_OBS...
          pose proof (ltProp_trichotomy hy hx) as [H_lt | [H_eq | H_gt]]...
          * rewrite <- ltb_lt in H_lt... right. right...
          * rewrite eqb_neq in H_OBS... contradiction H_OBS...
          * rewrite <- ltb_lt in H_gt...
    Qed.
    Next Obligation with eauto 2.
      simpl. reflexivity.
    Qed.
    Next Obligation with eauto 2.
      simpl in *. destruct (vectorGt y x) as [ | ]; split; intros ?; congruence.
    Qed.

  End VECTOR.

  Lemma Forall_True {A : Type} (xs : list A)
    : Forall (fun _ => True) xs.
  Proof.
    induction xs as [ | x xs IH]; eauto.
  Qed.

  Lemma vectorEq_true_iff `{hsEq_A : hsEq A (well_formed := fun _ => True)} (eqProp_spec : ∀ x : A, ∀ y : A, eqProp x y <-> x = y) (len : nat) (x : list A) (y : list A)
    (x_len : length x = len)
    (y_len : length y = len)
    : vectorEq x y = true <-> x = y.
  Proof.
    revert y len x_len y_len. induction x as [ | hx tx IH], y as [ | hy ty]; simpl; intros ? <- LEN_EQ; simpl; try congruence.
    - tauto.
    - destruct (eqb hx hy) as [ | ] eqn: H_OBS; rewrite eqb_obs in H_OBS; simpl; eauto 2.
      + rewrite eqProp_spec in H_OBS. rewrite IH; eauto 2. split; congruence.
      + rewrite eqProp_spec in H_OBS. split; congruence.
  Qed.

  Class has_value_of (A : Type) : Type :=
    value_of : A -> val.

  #[global] Arguments value_of {A} {has_value_of} _ /.

  #[global]
  Instance w64_has_value_of : has_value_of w64 :=
    fun x : w64 => #x.

  #[global] Arguments w64_has_value_of x /.

  #[global]
  Instance Slice_has_value_of : has_value_of Slice.t :=
    fun x : Slice.t => slice_val x.

  #[global] Arguments Slice_has_value_of x /.

End SessionPrelude.

Reserved Notation "x '!(' i ')'" (format "x  !( i )", left associativity, at level 1).

Module TypeVector.

  Inductive t : nat -> Type :=
    | nil : t O
    | cons {n: nat} (T: Type) {has_value_of: SessionPrelude.has_value_of T} (Ts: t n) : t (S n).

  Lemma case0 (P : TypeVector.t O -> Type)
    (P_nil : P (nil))
    : forall Ts, P Ts.
  Proof.
    intros Ts. revert P P_nil.
    exact (
      match Ts as Ts in TypeVector.t n return (match n as n return TypeVector.t n -> Type with O => fun Ts => forall P : TypeVector.t O -> Type, P nil -> P Ts | S n' => fun Ts => unit end) Ts with
      | nil => fun P => fun P_nil => P_nil
      | cons T' Ts' => tt
      end
    ).
  Defined.

  Lemma caseS {n' : nat} (P : TypeVector.t (S n') -> Type)
    (P_cons : forall T': Type, forall has_value_of: SessionPrelude.has_value_of T', forall Ts': TypeVector.t n', P (cons T' Ts'))
    : forall Ts, P Ts.
  Proof.
    intros Ts. revert P P_cons.
    exact (
      match Ts as Ts in TypeVector.t n return (match n as n return TypeVector.t n -> Type with O => fun Ts => unit | S n' => fun Ts => forall P : TypeVector.t (S n') -> Type, (forall T' : Type, forall has_value_of: SessionPrelude.has_value_of T', forall Ts' : TypeVector.t n', P (cons T' Ts')) -> P Ts end) Ts with
      | nil => tt
      | cons T' Ts' => fun P => fun P_cons => P_cons T' _ Ts'
      end
    ).
  Defined.

  Definition head {n} (Ts: TypeVector.t (S n)) : Type :=
    match Ts in TypeVector.t n' return
      match n' return Type with
      | O => unit
      | S n => Type
      end
    with
    | nil => tt
    | cons T' Ts' => T'
    end.

  Definition tail {n} (Ts: TypeVector.t (S n)) : TypeVector.t n :=
    match Ts in TypeVector.t n' return
      match n' return Type with
      | O => unit
      | S n => TypeVector.t n
      end
    with
    | nil => tt
    | cons T' Ts' => Ts'
    end.

  Fixpoint tuple_of (n: nat) {struct n} : forall Ts: TypeVector.t (S n), Type :=
    match n with
    | O => fun Ts => head Ts
    | S n => fun Ts => (tuple_of n (tail Ts) * head Ts)%type
    end.

  Fixpoint nthType {n} (i: nat) (Ts: TypeVector.t n) {struct Ts} : Type :=
    match Ts with
    | nil => unit
    | cons T' Ts' =>
      match i with
      | O => T'
      | S i' => nthType i' Ts'
      end
    end.

  Fixpoint nth (n: nat) (i: nat) {struct i}
    : forall Ts: TypeVector.t (S n), tuple_of n Ts -> nthType i Ts.
  Proof.
    destruct n as [ | n']; simpl.
    - induction Ts as [T' has_value_of Ts'] using TypeVector.caseS.
      induction Ts' as [] using TypeVector.case0.
      destruct i as [ | i']; simpl.
      + intros tuple. exact tuple.
      + intros tuple. exact tt.
    - induction Ts as [T' has_value_of Ts'] using TypeVector.caseS.
      destruct i as [ | i']; simpl.
      + intros tuple. exact (snd tuple).
      + intros tuple. exact (nth n' i' Ts' (fst tuple)).
  Defined.

  Definition lookup {n} {Ts} (tuple: tuple_of n Ts) i : nthType (n - i)%nat Ts :=
    nth n (n - i)%nat Ts tuple.

  Fixpoint magic (n: nat) {struct n} : forall Ts: TypeVector.t (S n), val -> tuple_of n Ts -> val :=
    match n with
    | O => TypeVector.caseS _ (fun T => fun has_value_of => fun Ts => fun v => fun tuple => (SessionPrelude.value_of tuple, v)%V)
    | S n => TypeVector.caseS _ (fun T => fun has_value_of => fun Ts => fun v => fun tuple => magic n Ts (SessionPrelude.value_of (snd tuple), v)%V (fst tuple))
    end.

  Ltac des H :=
    red in H; simpl in H; repeat lazymatch type of H with (_ * _)%type => destruct H as [H ?] end.

End TypeVector.

Declare Scope TypeVector_scope.
Bind Scope TypeVector_scope with TypeVector.t.

Notation "[ ]" := (TypeVector.nil) : TypeVector_scope.
Notation "[ T1 ]" := (TypeVector.cons T1 TypeVector.nil) : TypeVector_scope.
Notation "[ T1 , T2 , .. , Tn ]" := (TypeVector.cons Tn (.. (TypeVector.cons T2 (TypeVector.cons T1 TypeVector.nil)) ..)) : TypeVector_scope.

Notation "x !( i )" := (TypeVector.lookup x i).

Definition tuple_of {n: nat} (Ts: TypeVector.t (S n)) : Type :=
  TypeVector.tuple_of n Ts.

Arguments tuple_of {n} Ts : simpl never.

#[global]
Instance tuple_of_has_value_of {n} (Ts: TypeVector.t (S n)) : SessionPrelude.has_value_of (tuple_of Ts) :=
  TypeVector.magic n Ts #()%V.

Arguments tuple_of_has_value_of {n} Ts /.

#[global] Hint Unfold TypeVector.lookup SessionPrelude.w64_has_value_of SessionPrelude.Slice_has_value_of : session_hints.

Ltac simplNotation :=
  autounfold with session_hints in *; simpl in *.
