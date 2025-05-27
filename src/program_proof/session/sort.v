From Perennial.program_proof.session Require Export session_prelude.
From Perennial.program_proof.session Require Export coq_session.
From Perennial.program_proof.session Require Export versionVector.

Section heap.
  Context `{hG: !heapGS Σ}.

  Definition mapOperationVersionVector (l: list Operation.t) :=
    map (fun op => op.(Operation.VersionVector)) l.

  Variant binarySearch_spec (needle: Operation.t) (l: list Operation.t) (n: nat) (r: nat) : Prop :=
    | binarySearch_spec_intro prefix suffix
      (LENGTH: r = length prefix)
      (VECTOR: mapOperationVersionVector l = mapOperationVersionVector (if forallb (fun x => negb (coq_equalSlices x.(Operation.VersionVector) needle.(Operation.VersionVector))) l then prefix ++ suffix else prefix ++ [needle] ++ suffix))
      (PREFIX: ∀ op, In op prefix -> coq_lexicographicCompare needle.(Operation.VersionVector) op.(Operation.VersionVector) = true)
      (SUFFIX: ∀ op, In op suffix -> coq_lexicographicCompare op.(Operation.VersionVector) needle.(Operation.VersionVector) = true)
      : binarySearch_spec needle l n r.

  Lemma wp_binarySearch (s: Slice.t) (l: list Operation.t) (opv: Slice.t*u64) (needle: Operation.t) (n: nat) :
    {{{
        operation_slice s l n ∗
        is_operation opv needle n ∗
        ⌜is_sorted l⌝
    }}}
      CoqSessionServer.binarySearch (slice_val s) (operation_val opv)
    {{{
        (pos: u64), RET #pos;
        operation_slice s l n ∗
        is_operation opv needle n ∗
        ⌜binarySearch_spec needle l n (uint.nat pos)⌝
    }}}.
  Proof.
    iIntros "%Φ (H_s & H_n & %SORTED) HΦ". rewrite /binarySearch. wp_pures.
    wp_apply wp_ref_to. { eauto. } iIntros "%i H_i". wp_pures.
    wp_apply wp_slice_len. wp_pures. wp_apply wp_ref_to. { eauto. } iIntros "%j H_j". wp_pures.
    wp_apply (wp_forBreak_cond
      ( λ continue, ∃ i_val : w64, ∃ j_val : w64,
        operation_slice s l n ∗
        is_operation opv needle n ∗
        i ↦[uint64T] #i_val ∗
        j ↦[uint64T] #j_val ∗
        ⌜(0 <= uint.Z i_val)%Z⌝ ∗
        ⌜(0 <= uint.Z j_val)%Z⌝ ∗
        ⌜(uint.nat i_val <= uint.nat j_val)%nat⌝ ∗
        ⌜(uint.nat j_val <= length l)%nat⌝ ∗
        ⌜∀ op, In op (take (uint.nat i_val) l) -> coq_lexicographicCompare needle.(Operation.VersionVector) op.(Operation.VersionVector) = true⌝ ∗
        ⌜∀ op, In op (drop (uint.nat j_val) l) -> coq_lexicographicCompare op.(Operation.VersionVector) needle.(Operation.VersionVector) = true \/ needle.(Operation.VersionVector) = op.(Operation.VersionVector)⌝ ∗
        ⌜continue = false -> (uint.nat i_val = uint.nat j_val)%nat⌝
      )%I
    with "[] [H_s H_n H_i H_j]").
    { clear Φ. iIntros "%Φ". iModIntro. iIntros "(%i_val & %j_val & H_s & H_n & H_i & H_j & %i_ge_0 & %j_ge_0 & %i_bound & %j_bound & %H_prefix & %H_suffix & %H_continue) HΦ". wp_pures. wp_load. wp_load. wp_if_destruct.
      - wp_pures. wp_load. wp_load. wp_load. iDestruct "H_s" as "(%ops & H_s & H_ops)". iPoseProof (big_sepL2_length with "[$H_ops]") as"%H_ops_len". iPoseProof (own_slice_sz with "[$H_s]") as "%H_s_sz". iDestruct "H_s" as "[H1_s H2_s]".
        assert (uint.nat (w64_word_instance .(word.add) i_val (w64_word_instance .(word.divu) (w64_word_instance .(word.sub) j_val i_val) (W64 2))) < length ops)%nat as H_mid by now rewrite H_ops_len; word.
        pose proof (lookup_lt_is_Some_2 _ _ H_mid) as [x H_x]. iPoseProof (big_sepL2_middle_split _ H_x with "[$H_ops]") as "H_ops". iDestruct "H_ops" as "(%mid & %prefix & %suffix & [%H_l %H_length] & MID & PREFIX & SUFFIX)".
        wp_apply (wp_SliceGet with "[$H1_s]"); auto. iIntros "H1_s". iDestruct "H_n" as "(%H1_n & %H2_n & H3_n)". iDestruct "MID" as "(%H1_m & %H2_m & H3_m)". wp_apply (wp_lexicographicCompare with "[$H3_n $H3_m]"). { iPureIntro; word. }
        iIntros "%r (H3_n & H3_m & %H_r)". subst r. wp_if_destruct.
        + wp_store. iModIntro. iApply "HΦ". iFrame. iSplitR "".
          { subst l. iApply (big_sepL2_middle_merge with "[$PREFIX $SUFFIX $H3_m]"); eauto. }
          iPureIntro. repeat (split; (word || trivial)). intros op H_IN. apply SessionPrelude.In_lookup in H_IN. destruct H_IN as (k & LOOKUP & H_k).
          set (m := (w64_word_instance .(word.add) i_val (w64_word_instance .(word.divu) (w64_word_instance .(word.sub) j_val i_val) (W64 2)))) in *.
          assert (k = uint.nat m \/ k < uint.nat m) as [k_EQ | k_LT] by now rewrite length_take in H_k; revert H_k; word.
          * subst k. rewrite lookup_take in LOOKUP; try word. rewrite H_l in LOOKUP. rewrite lookup_app_r in LOOKUP; try word.
            replace (uint.nat m - length prefix)%nat with 0%nat in LOOKUP by word. simpl in LOOKUP. assert (op = mid) as -> by congruence; trivial.
          * eapply aux0_lexicographicCompare with (l2 := mid.(Operation.VersionVector)); trivial. rewrite lookup_take in LOOKUP; try word. eapply SORTED with (i := k) (j := length prefix); word || trivial.
            rewrite H_l. rewrite lookup_app_r; try word. replace (length prefix - length prefix)%nat with 0%nat by word; trivial.
        + wp_store. iModIntro. iApply "HΦ". iFrame. iSplitR "".
          { subst l. iApply (big_sepL2_middle_merge with "[$PREFIX $SUFFIX $H3_m]"); eauto. }
          iPureIntro. repeat (split; (word || trivial)). intros op H_IN. apply SessionPrelude.In_lookup in H_IN. destruct H_IN as (k & LOOKUP & H_k).
          assert (length needle .(Operation.VersionVector) = length mid .(Operation.VersionVector)) as H_len by word.
          assert (k = 0 \/ k > 0)%nat as [k_EQ | k_GT] by word.
          * subst k. rewrite H_l in LOOKUP. rewrite <- H_length in LOOKUP. rewrite lookup_drop in LOOKUP. rewrite lookup_app_r in LOOKUP; try word.
            replace (length prefix + 0 - length prefix)%nat with 0%nat in LOOKUP by word. simpl in LOOKUP. assert (op = mid) as -> by congruence; clear LOOKUP.
            pose proof (aux6_lexicographicCompare _ _ H_len Heqb0) as [H_GT | H_EQ]; [left | right]; done.
          * assert (coq_lexicographicCompare mid.(Operation.VersionVector) needle.(Operation.VersionVector) = true \/ needle.(Operation.VersionVector) = mid.(Operation.VersionVector)) as [GT | EQ].
            { eapply aux6_lexicographicCompare; trivial. }
            { rewrite lookup_drop in LOOKUP; try word. set (m := (uint.nat (w64_word_instance .(word.add) i_val (w64_word_instance .(word.divu) (w64_word_instance .(word.sub) j_val i_val) (W64 2))))) in *. left. eapply aux0_lexicographicCompare; try eassumption.
              eapply SORTED with (i := m) (j := (m + k)%nat); try word; trivial. rewrite -> H_l. rewrite <- H_length. rewrite lookup_app_r; try word. replace (length prefix - length prefix)%nat with 0%nat by word; trivial. }
            { rewrite -> EQ. left. rewrite lookup_drop in LOOKUP. set (m := uint.nat (w64_word_instance .(word.add) i_val (w64_word_instance .(word.divu) (w64_word_instance .(word.sub) j_val i_val) (W64 2)))). eapply SORTED with (i := m) (j := (m + k)%nat); word || trivial. unfold m. rewrite <- H_length.
              rewrite H_l. rewrite lookup_app_r; try word. replace (length prefix - length prefix)%nat with 0%nat by word; trivial. }
      - iModIntro. iApply "HΦ". iFrame. iPureIntro. repeat (split; (word || trivial)).
    }
    { iDestruct "H_s" as "(%ops & H_s & H_ops)". iPoseProof (big_sepL2_length with "[$H_ops]") as"%H_ops_len". iPoseProof (own_slice_sz with "[$H_s]") as "%H_s_sz".
      iFrame. iPureIntro. repeat (split; (word || trivial)).
      - replace (uint.nat (W64 0)) with 0%nat by word. simpl. tauto.
      - rewrite <- H_s_sz, -> H_ops_len. replace (drop (length l) l) with ( @nil Operation.t); simpl; try tauto. symmetry. eapply nil_length_inv. rewrite length_drop. word.
    }
    { iIntros "(%i_val & %j_val & H_s & H_n & H_i & H_j & %i_ge_0 & %j_ge_0 & %i_bound & %j_bound & %H_prefix & %H_suffix & %H_continue)". specialize (H_continue eq_refl). assert (i_val = j_val) as <- by word. destruct (forallb (fun x => negb (coq_equalSlices x.(Operation.VersionVector) needle.(Operation.VersionVector))) l) as [ | ] eqn: H_OBS.
      - wp_load. iModIntro. iApply "HΦ". iFrame. iPureIntro. exists (take (uint.nat i_val) l) (drop (uint.nat i_val) l).
        + rewrite length_take. word.
        + rewrite H_OBS. rewrite take_drop. trivial.
        + trivial.
        + rewrite SessionPrelude.forallb_spec in H_OBS. intros op H_op. assert (In op l) as H_IN. { apply SessionPrelude.In_lookup in H_op. destruct H_op as (k & LOOKUP & H_k). rewrite lookup_drop in LOOKUP. eapply SessionPrelude.lookup_In. eassumption. }
          apply H_OBS in H_IN. rewrite negb_true_iff in H_IN. pose proof (H_suffix op H_op) as [? | EQ]; trivial. rewrite EQ in H_IN. rewrite -> aux3_equalSlices in H_IN. congruence. 
      - wp_load. iModIntro. iApply "HΦ". iPoseProof (pers_is_operation with "[$H_n]") as "(%H1_n & %H2_n & #H3_n)".
        pose proof (COPY := H_OBS). rewrite SessionPrelude.forallb_spec in COPY. destruct COPY as (x & x_in & H_x).
        rewrite negb_false_iff in H_x. apply SessionPrelude.In_lookup in x_in. destruct x_in as (k & LOOKUP & H_k).
        iPoseProof (op_versionVector_len with "H_s") as "%VIEW". pose proof (VIEW k x LOOKUP) as LENGTH. iFrame. iPureIntro. exists (take (uint.nat i_val) l) (drop (uint.nat i_val + 1)%nat l).
        + rewrite length_take. word.
        + rewrite H_OBS. unfold mapOperationVersionVector. do 2 rewrite map_app. eapply SessionPrelude.list_ext.
          { do 2 rewrite length_app. simpl. repeat rewrite length_map. rewrite length_take. rewrite length_drop. enough (uint.nat i_val + 1 <= length l)%nat by word. enough (uint.nat i_val ≠ length l)%nat by word.
            intros H_contra. rewrite <- H_contra in H_k. assert (H_IN : In x (take (uint.nat i_val) l)). { eapply SessionPrelude.lookup_In. rewrite lookup_take; eauto. word. }
            apply H_prefix in H_IN. pose proof (aux4_lexicographicCompare _ _ H_IN) as H_CONTRA; apply aux2_equalSlices in H_CONTRA; try congruence.
          }
          clear i j. intros i op1 op2 [H_op1 H_op2]. assert (i < uint.nat i_val \/ i = uint.nat i_val \/ i > uint.nat i_val) as [LT | [EQ | GT]] by word.
          { rewrite lookup_app_l in H_op2; cycle 1. { rewrite length_map. rewrite length_take; word. } rewrite -> SessionPrelude.lookup_map in H_op1, H_op2. rewrite lookup_take in H_op2; try congruence. word. }
          { rewrite lookup_app_r in H_op2; cycle 1. { rewrite length_map. rewrite length_take; word. } replace (i - length (map (λ op : Operation.t, op .(Operation.VersionVector)) (take (uint.nat i_val) l)))%nat with 0%nat in H_op2; cycle 1. { rewrite length_map. rewrite length_take; word. }
            simpl in H_op2. subst i. assert (op2 = needle.(Operation.VersionVector)) as -> by congruence. clear H_op2. assert (k < uint.nat i_val \/ k = uint.nat i_val \/ k > uint.nat i_val)%nat as [k_LT | [k_EQ | k_GT]] by word.
            - rewrite SessionPrelude.lookup_map in H_op1. destruct (l !! uint.nat i_val) as [y | ] eqn: H_y; try congruence. assert (op1 = y.(Operation.VersionVector)) as -> by congruence. pose proof (SORTED k (uint.nat i_val) k_LT _ _ LOOKUP H_y) as H_contra1.
              assert (In x (take (uint.nat i_val) l)) as H_IN. { eapply SessionPrelude.lookup_In. rewrite lookup_take; eauto. } apply H_prefix in H_IN. apply aux2_equalSlices in H_x; try word. pose proof (aux5_lexicographicCompare _ _ H_x); congruence.
            - subst k. rewrite SessionPrelude.lookup_map in H_op1. destruct (l !! uint.nat i_val) as [y | ] eqn: H_y; try congruence. assert (op1 = y.(Operation.VersionVector)) as -> by congruence. clear H_op1. assert (x = y) as <- by congruence. clear LOOKUP. eapply aux0_equalSlices; eauto. word.
            - rewrite SessionPrelude.lookup_map in H_op1. destruct (l !! uint.nat i_val) as [y | ] eqn: H_y; try congruence. assert (op1 = y.(Operation.VersionVector)) as -> by congruence. pose proof (SORTED (uint.nat i_val) k k_GT _ _ H_y LOOKUP) as H_contra1.
              assert (In y (drop (uint.nat i_val) l)) as H_IN. { eapply SessionPrelude.lookup_In with (n := 0%nat). rewrite lookup_drop; eauto. rewrite Nat.add_0_r; trivial. } apply H_suffix in H_IN. destruct H_IN; try done. rewrite aux4_lexicographicCompare in H_x; try congruence. eapply aux0_lexicographicCompare; eauto.
          }
          { rewrite lookup_app_r in H_op2; cycle 1. { rewrite length_map. rewrite length_take; word. }  rewrite length_map in H_op2. rewrite length_take in H_op2. rewrite lookup_app_r in H_op2; cycle 1. { rewrite length_map. simpl. word. } rewrite length_map in H_op2. simpl in H_op2. enough (Some op1 = Some op2) by congruence.
            rewrite SessionPrelude.lookup_map in H_op1. destruct (l !! i) as [y | ] eqn: H_y; try congruence. rewrite SessionPrelude.lookup_map in H_op2. rewrite lookup_drop in H_op2. replace (uint.nat i_val + 1 + (i - uint.nat i_val `min` length l - 1))%nat with i in H_op2 by word. rewrite H_y in H_op2. congruence.
          }
        + trivial.
        + intros op H_op. apply SessionPrelude.In_lookup in H_op. clear i j. destruct H_op as (i & LOOKUP1 & H_i). rewrite length_drop in H_i. assert (uint.nat i_val < length l)%nat as LT by word.
          pose proof (SessionPrelude.lookup_Some l (uint.nat i_val) LT) as (op' & LOOKUP2). assert (In op' (drop (uint.nat i_val) l)) as H_IN. { eapply SessionPrelude.lookup_In with (n := 0%nat). rewrite lookup_drop. rewrite <- LOOKUP2. f_equal; word. } pose proof (H_suffix op' H_IN) as [op_LT | op_EQ].
          * eapply aux0_lexicographicCompare; eauto. rewrite lookup_drop in LOOKUP1. eapply SORTED with (i := uint.nat i_val) (j := (uint.nat i_val + 1 + i)%nat); word || trivial.
          * rewrite op_EQ. rewrite lookup_drop in LOOKUP1. eapply SORTED with (i := uint.nat i_val) (j := (uint.nat i_val + 1 + i)%nat); word || trivial.
    }
  Qed.

  Lemma wp_sortedInsert s l o v n :
    {{{
        operation_slice s l n ∗
        is_operation o v n ∗
        ⌜is_sorted l⌝ 
    }}}
      CoqSessionServer.sortedInsert (slice_val s) (operation_val o)
    {{{
        ns, RET (slice_val ns);
        operation_slice ns (coq_sortedInsert l v) n ∗
        ⌜is_sorted (coq_sortedInsert l v)⌝
    }}}.
  Proof.
  Admitted.

End heap.

#[global] Opaque wp_binarySearch.
#[global] Opaque wp_sortedInsert.
