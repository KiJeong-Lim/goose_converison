From Perennial.program_proof.session Require Export session_prelude coq_session versionVector.

Section heap.
  Context `{hG: !heapGS Σ}.

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
      - wp_load. iModIntro. iApply "HΦ". iFrame. iPureIntro. exists (map getOperationVersionVector (take (uint.nat i_val) l)) (map getOperationVersionVector (drop (uint.nat i_val) l)).
        + rewrite length_map. rewrite length_take. word.
        + rewrite H_OBS. rewrite <- map_app. rewrite take_drop. trivial.
        + intros op H_op. rewrite in_map_iff in H_op. destruct H_op as (x & <- & IN). eapply H_prefix. trivial.
        + rewrite SessionPrelude.forallb_spec in H_OBS. intros op H_op. assert (In op (map getOperationVersionVector l)) as H_IN. { apply SessionPrelude.In_lookup in H_op. destruct H_op as (k & LOOKUP & H_k). rewrite SessionPrelude.map_drop in LOOKUP. rewrite lookup_drop in LOOKUP. eapply SessionPrelude.lookup_In. eassumption. }
          rewrite in_map_iff in H_IN. destruct H_IN as (x & <- & H_IN). apply H_OBS in H_IN. rewrite negb_true_iff in H_IN. rewrite in_map_iff in H_op. destruct H_op as (y & x_eq_y & IN). unfold getOperationVersionVector in x_eq_y |- *. pose proof (H_suffix y IN) as [? | EQ]; try congruence. rewrite EQ in H_IN. rewrite -> x_eq_y in H_IN. now rewrite -> aux3_equalSlices in H_IN. 
      - wp_load. iModIntro. iApply "HΦ". iPoseProof (pers_is_operation with "[$H_n]") as "(%H1_n & %H2_n & #H3_n)".
        pose proof (COPY := H_OBS). rewrite SessionPrelude.forallb_spec in COPY. destruct COPY as (x & x_in & H_x).
        rewrite negb_false_iff in H_x. apply SessionPrelude.In_lookup in x_in. destruct x_in as (k & LOOKUP & H_k).
        iPoseProof (op_versionVector_len with "H_s") as "%VIEW". pose proof (VIEW k x LOOKUP) as LENGTH. iFrame. iPureIntro. exists (map getOperationVersionVector (take (uint.nat i_val) l)) (map getOperationVersionVector (drop (uint.nat i_val + 1)%nat l)).
        + rewrite length_map. rewrite length_take. word.
        + rewrite H_OBS. eapply SessionPrelude.list_ext.
          { do 2 rewrite length_app. simpl. repeat rewrite length_map. rewrite length_take. rewrite length_drop. enough (uint.nat i_val + 1 <= length l)%nat by word. enough (uint.nat i_val ≠ length l)%nat by word.
            intros H_contra. rewrite <- H_contra in H_k. assert (H_IN : In x (take (uint.nat i_val) l)). { eapply SessionPrelude.lookup_In. rewrite lookup_take; eauto. word. }
            apply H_prefix in H_IN. pose proof (aux4_lexicographicCompare _ _ H_IN) as H_CONTRA; apply aux2_equalSlices in H_CONTRA; try congruence. rewrite LENGTH. destruct H2_n; word.
          }
          clear i j. intros i op1 op2 [H_op1 H_op2]. assert (i < uint.nat i_val \/ i = uint.nat i_val \/ i > uint.nat i_val) as [LT | [EQ | GT]] by word.
          { rewrite lookup_app_l in H_op2; cycle 1. { rewrite length_map. rewrite length_take; word. } rewrite -> SessionPrelude.lookup_map in H_op1, H_op2. rewrite lookup_take in H_op2; try congruence. word. }
          { rewrite lookup_app_r in H_op2; cycle 1. { rewrite length_map. rewrite length_take; word. } replace (i - length (map getOperationVersionVector (take (uint.nat i_val) l)))%nat with 0%nat in H_op2; cycle 1. { rewrite length_map. rewrite length_take; word. }
            simpl in H_op2. subst i. unfold getOperationVersionVector in H_op2. assert (op2 = needle.(Operation.VersionVector)) as -> by congruence. clear H_op2. assert (k < uint.nat i_val \/ k = uint.nat i_val \/ k > uint.nat i_val)%nat as [k_LT | [k_EQ | k_GT]] by word.
            - rewrite SessionPrelude.lookup_map in H_op1. destruct (l !! uint.nat i_val) as [y | ] eqn: H_y; try congruence. unfold getOperationVersionVector in H_op1. assert (op1 = y.(Operation.VersionVector)) as -> by congruence. pose proof (SORTED k (uint.nat i_val) k_LT _ _ LOOKUP H_y) as H_contra1.
              assert (In x (take (uint.nat i_val) l)) as H_IN. { eapply SessionPrelude.lookup_In. rewrite lookup_take; eauto. } apply H_prefix in H_IN. apply aux2_equalSlices in H_x; try word. pose proof (aux5_lexicographicCompare _ _ H_x); congruence.
            - subst k. rewrite SessionPrelude.lookup_map in H_op1. destruct (l !! uint.nat i_val) as [y | ] eqn: H_y; try congruence. unfold getOperationVersionVector in H_op1. assert (op1 = y.(Operation.VersionVector)) as -> by congruence. clear H_op1. assert (x = y) as <- by congruence. clear LOOKUP. eapply aux0_equalSlices; eauto. word.
            - rewrite SessionPrelude.lookup_map in H_op1. destruct (l !! uint.nat i_val) as [y | ] eqn: H_y; try congruence. unfold getOperationVersionVector in H_op1. assert (op1 = y.(Operation.VersionVector)) as -> by congruence. pose proof (SORTED (uint.nat i_val) k k_GT _ _ H_y LOOKUP) as H_contra1.
              assert (In y (drop (uint.nat i_val) l)) as H_IN. { eapply SessionPrelude.lookup_In with (n := 0%nat). rewrite lookup_drop; eauto. rewrite Nat.add_0_r; trivial. } apply H_suffix in H_IN. destruct H_IN; try done. rewrite aux4_lexicographicCompare in H_x; try congruence. eapply aux0_lexicographicCompare; eauto.
          }
          { rewrite lookup_app_r in H_op2; cycle 1. { rewrite length_map. rewrite length_take; word. }  rewrite length_map in H_op2. rewrite length_take in H_op2. rewrite lookup_app_r in H_op2; cycle 1. { simpl. word. } simpl in H_op2. enough (Some op1 = Some op2) by congruence.
            rewrite SessionPrelude.lookup_map in H_op1. destruct (l !! i) as [y | ] eqn: H_y; try congruence. rewrite SessionPrelude.lookup_map in H_op2. rewrite lookup_drop in H_op2. replace (uint.nat i_val + 1 + (i - uint.nat i_val `min` length l - 1))%nat with i in H_op2 by word. rewrite H_y in H_op2. congruence.
          }
        + intros op H_op. rewrite in_map_iff in H_op. destruct H_op as (y & <- & IN). eapply H_prefix. trivial.
        + intros op H_op. apply SessionPrelude.In_lookup in H_op. clear i j. destruct H_op as (i & LOOKUP1 & H_i). rewrite length_map in H_i. rewrite length_drop in H_i. assert (uint.nat i_val < length l)%nat as LT by word.
          pose proof (SessionPrelude.lookup_Some l (uint.nat i_val) LT) as (op' & LOOKUP2). assert (In op' (drop (uint.nat i_val) l)) as H_IN. { eapply SessionPrelude.lookup_In with (n := 0%nat). rewrite lookup_drop. rewrite <- LOOKUP2. f_equal; word. } pose proof (H_suffix op' H_IN) as [op_LT | op_EQ].
          * eapply aux0_lexicographicCompare; eauto. rewrite SessionPrelude.map_drop in LOOKUP1. rewrite lookup_drop in LOOKUP1. rewrite SessionPrelude.lookup_map in LOOKUP1. destruct (l !! (uint.nat i_val + 1 + i)%nat) as [z | ] eqn: H_z; try congruence. unfold getOperationVersionVector in LOOKUP1. assert (op = z.(Operation.VersionVector)) as -> by congruence. eapply SORTED with (i := uint.nat i_val) (j := (uint.nat i_val + 1 + i)%nat); word || trivial.
          * rewrite op_EQ. rewrite SessionPrelude.map_drop in LOOKUP1. rewrite lookup_drop in LOOKUP1. rewrite SessionPrelude.lookup_map in LOOKUP1. destruct (l !! (uint.nat i_val + 1 + i)%nat) as [z | ] eqn: H_z; try congruence. unfold getOperationVersionVector in LOOKUP1. assert (op = z.(Operation.VersionVector)) as -> by congruence. eapply SORTED with (i := uint.nat i_val) (j := (uint.nat i_val + 1 + i)%nat); word || trivial.
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
    iIntros "%Φ (H_s & H_n & %SORTED) HΦ". rewrite /sortedInsert. wp_pures.
    wp_apply (wp_binarySearch with "[$H_s $H_n]"); eauto. iIntros "%pos (H_s & H_n & %H_pos)".
    iPoseProof (op_versionVector_len with "[$H_s]") as "%claim1". wp_apply wp_slice_len. wp_if_destruct.
    { replace operation_val with operation_into_val.(to_val) by reflexivity. iDestruct "H_s" as "(%ops & H_s & H_ops)". iPoseProof (big_sepL2_length with "[$H_ops]") as "%H_ops_len". iPoseProof (own_slice_sz with "[$H_s]") as "%H_s_sz". iPoseProof (Forall_Operation_wf with "H_ops") as "%claim2". iPoseProof (Operation_wf_INTRO with "[$H_n]") as "%claim3".
      wp_apply (wp_SliceAppend with "[$H_s]"). iIntros "%s' H_s'". iApply "HΦ". replace (coq_sortedInsert l v) with (l ++ [v]).
      - iFrame. simpl. iPureIntro. split; trivial. rewrite <- H_s_sz in H_pos. rewrite -> H_ops_len in H_pos. destruct H_pos. destruct (forallb _) as [ | ] eqn: H_OBS.
        + pose proof ( @f_equal (list (list u64)) nat length _ _ VECTOR) as H_length. rewrite length_map in H_length. rewrite length_app in H_length.
          assert (length suffix = 0%nat) as H_suffix_len by word. destruct suffix; simpl in *; try word. clear H_suffix_len H_length SUFFIX. rewrite app_nil_r in VECTOR.
          intros i j LT o1 o2 H_o1 H_o2. rewrite SessionPrelude.lookup_app in H_o2. destruct (Nat.ltb j (length l)) as [ | ] eqn: H_ltb; [rewrite Nat.ltb_lt in H_ltb | rewrite Nat.ltb_nlt in H_ltb].
          * rewrite SessionPrelude.lookup_app in H_o1. replace (i <? length l)%nat with true in H_o1 by now symmetry; rewrite Nat.ltb_lt; word. eapply SORTED with (i := i) (j := j); trivial.
          * rewrite SessionPrelude.lookup_one in H_o2. destruct H_o2 as [<- H_eq_0]. eapply PREFIX. rewrite <- VECTOR. rewrite in_map_iff. exists o1. split; trivial. rewrite SessionPrelude.lookup_app in H_o1. replace (Nat.ltb i (length l)) with true in H_o1 by now symmetry; rewrite Nat.ltb_lt; word. eapply SessionPrelude.lookup_In; eassumption.
        + pose proof ( @f_equal (list (list u64)) nat length _ _ VECTOR) as H_length. rewrite length_map in H_length. rewrite length_app in H_length. simpl in H_length. word.
      - rewrite -> redefine_coq_sortedInsert with (len := n). pose proof (SessionPrelude.sortedInsert_unique (well_formed := Operation_wf n) l v claim2 claim3 l [] SORTED) as claim4. simpl in claim4. rewrite app_nil_r in claim4. specialize (claim4 eq_refl). destruct H_pos. change SessionPrelude.vectorGt with coq_lexicographicCompare in *. change SessionPrelude.vectorEq with coq_equalSlices in *.
        assert (length l = length prefix) as claim5 by word. destruct (forallb _) as [ | ] eqn: H_forallb; rewrite SessionPrelude.forallb_spec in H_forallb.
        + rewrite app_nil_r in claim4. symmetry. eapply claim4.
          * intros m x H_x. eapply PREFIX. pose proof (COPY := VECTOR). apply f_equal with (f := length) in COPY. rewrite length_app in COPY. rewrite length_map in COPY. assert (suffix = []) as -> by now eapply nil_length_inv; word. rewrite -> app_nil_r in *.
            rewrite <- VECTOR. rewrite in_map_iff. exists x. split; trivial. eapply SessionPrelude.lookup_In; eassumption.
          * intros [ | ?]; simpl in *; intros; try congruence.
        + destruct H_forallb as (x & IN & H_in). rewrite -> negb_false_iff in H_in. pose proof (COPY := VECTOR). apply f_equal with (f := length) in COPY. rewrite length_app in COPY. rewrite length_map in COPY. simpl in *. word.
    }
    iDestruct "H_s" as "(%ops & H_s & H_ops)". iPoseProof (own_slice_cap_wf with "[H_s]") as "%H_cap". { iDestruct "H_s" as "[H1_s H2_s]". iExact "H2_s". } iPoseProof (big_sepL2_length with "[$H_ops]") as "%H_ops_len". iPoseProof (own_slice_sz with "[$H_s]") as "%H_s_sz". iPoseProof (Forall_Operation_wf with "H_ops") as "%claim2". iPoseProof (Operation_wf_INTRO with "[$H_n]") as "%claim3". destruct H_pos. assert (uint.nat pos < length l)%nat as claim4. { destruct (forallb _) as [ | ]; apply f_equal with (f := length) in VECTOR; rewrite length_map in VECTOR; simpl in *; rewrite length_app in VECTOR; try word. }
    pose proof (COPY := claim4). apply SessionPrelude.lookup_Some in COPY. destruct COPY as (x & LOOKUP). iPoseProof (big_sepL2_flip with "[$H_ops]") as "H_ops". iPoseProof (big_sepL2_middle_split _ LOOKUP with "[$H_ops]") as "(%v' & %prefix' & %suffix' & [%H_ops %H_len] & H_v' & H_prefix' & H_suffix')". iDestruct "H_s" as "[H1_s H2_s]".
    assert (ops !! uint.nat pos = Some v') by now rewrite H_ops; rewrite -> lookup_app_r; try word; replace (uint.nat pos - length prefix')%nat with 0%nat by word; trivial. wp_apply (wp_SliceGet with "[$H1_s]"); eauto. iIntros "H1_s". wp_pures. rename v' into o', x into v'. iRename "H_n" into "H_v". iPoseProof (pers_is_operation with "[$H_v]") as "(%H1_pers_v & %H2_pers_v & #H3_pers_v)". iPoseProof (pers_is_operation with "[$H_v']") as "(%H1_pers_v' & %H2_pers_v' & #H3_pers_v')". wp_apply (wp_equalSlices _ v'.(Operation.VersionVector) _ v.(Operation.VersionVector)). { iSplit. { iExact "H3_pers_v'". } iSplitL. { iExact "H3_pers_v". } iPureIntro. word. } iIntros "%r (H3_v' & H3_v & %H_r)". wp_if_destruct; subst r.
    { iModIntro. iApply "HΦ". replace (coq_sortedInsert l v) with l.
      - iFrame. iSplitR "".
        + iApply big_sepL2_flip. rewrite H_ops. iApply big_sepL2_middle_merge; eauto.
        + iPureIntro; trivial.
      - pose proof (SessionPrelude.sortedInsert_unique (well_formed := Operation_wf n) l v claim2 claim3 (take (uint.nat pos) l) (drop (uint.nat pos) l) SORTED) as claim5. simpl in claim5. rewrite -> take_drop with (l := l) (i := uint.nat pos) in claim5. specialize (claim5 eq_refl).
        change SessionPrelude.vectorGt with coq_lexicographicCompare in *. change SessionPrelude.vectorEq with coq_equalSlices in *. destruct (forallb _) as [ | ] eqn: H_forallb; rewrite SessionPrelude.forallb_spec in H_forallb.
        + assert (In v' l) as IN. { eapply SessionPrelude.lookup_In. eassumption. } apply H_forallb in IN. rewrite negb_true_iff in IN. congruence.
        + simpl in *. rewrite take_drop in claim5. symmetry. eapply claim5.
          * intros m y H_m. pose proof (proj1 (List.Forall_forall (Operation_wf n) l) claim2 y) as y_wf. rewrite <- take_drop with (l := l) (i := uint.nat pos) in y_wf. rewrite in_app_iff in y_wf. specialize (y_wf (or_introl (SessionPrelude.lookup_In _ _ _ H_m))). eapply PREFIX. pose proof (COPY := VECTOR). apply f_equal with (f := take (uint.nat pos)) in COPY.
            assert (IN' : In y.(Operation.VersionVector) (map getOperationVersionVector l)). { rewrite in_map_iff. exists y. split; trivial. rewrite <- take_drop with (l := l) (i := uint.nat pos). rewrite in_app_iff. left. eapply SessionPrelude.lookup_In. eassumption. }
            rewrite VECTOR in IN'. rewrite in_app_iff in IN'. destruct IN' as [IN' | IN']; trivial. assert (m < length (take (uint.nat pos) l))%nat as claim6. { eapply lookup_lt_is_Some_1. exists y; trivial. } apply SessionPrelude.In_lookup in IN'. destruct IN' as (j & LOOKUP' & H_j).
            assert (j + uint.nat pos < length (map getOperationVersionVector l))%nat as j_bound. { rewrite VECTOR. rewrite length_app. word. } rewrite length_map in j_bound. pose proof (SessionPrelude.lookup_Some l (j + uint.nat pos)%nat j_bound) as (z & H_z). assert (Operation_wf n z) as z_wf. { eapply List.Forall_forall; try eassumption. eapply SessionPrelude.lookup_In; eassumption. }
            assert (y.(Operation.VersionVector) = z.(Operation.VersionVector)) as EQ. { enough (Some y.(Operation.VersionVector) = Some z.(Operation.VersionVector)) as EQ by congruence. rewrite <- LOOKUP'. pose proof (SessionPrelude.lookup_map getOperationVersionVector l (j + uint.nat pos)%nat) as claim7. rewrite H_z in claim7. rewrite VECTOR in claim7. rewrite lookup_app_r in claim7; try word. replace (j + uint.nat pos - length prefix)%nat with j in claim7 by word. exact claim7. }
            contradiction (SessionPrelude.ltProp_irreflexivity (well_formed := Operation_wf n) y z); trivial. { do 3 red. unfold getOperationVersionVector. rewrite EQ. eapply @SessionPrelude.eqProp_reflexivity; trivial. } rewrite <- SessionPrelude.ltb_lt; trivial. rewrite length_take in claim6. rewrite lookup_take in H_m; try word. eapply SORTED with (i := m) (j := (j + uint.nat pos)%nat); word || trivial.
          * intros m y H_m. rewrite lookup_drop in H_m. pose proof (SessionPrelude.lookup_map getOperationVersionVector l (uint.nat pos + m)%nat) as VIEW. rewrite H_m in VIEW. rewrite VECTOR in VIEW. rewrite lookup_app_r in VIEW; try word. replace (uint.nat pos + m - length prefix)%nat with m in VIEW by word. assert (IN' : In y l). { eapply SessionPrelude.lookup_In; eassumption. } pose proof (proj1 (List.Forall_forall (Operation_wf n) l) claim2 y IN'). destruct m as [ | m]; simpl in *.
            { unfold getOperationVersionVector in VIEW. unfold getOperationVersionVector. replace (v.(Operation.VersionVector)) with (y.(Operation.VersionVector)) by congruence. right. eapply aux3_equalSlices. }
            { left. eapply SUFFIX. eapply SessionPrelude.lookup_In; eassumption. }
    }
    { wp_apply (wp_SliceSkip); try word. wp_apply slice.wp_SliceSingleton; eauto. iIntros "%s1 H_s1". replace [operation_val o] with ( @list.untype _ _ operation_into_val [o]) by reflexivity. iPoseProof (slice_small_split _ pos with "[$H1_s]") as "[H_s1_prefix H_s1_suffix]"; try word. wp_apply (wp_SliceAppendSlice with "[$H_s1 $H_s1_suffix]"). { repeat econstructor; eauto. } assert (drop (uint.nat pos) l = v' :: drop (uint.nat pos + 1)%nat l) as claim6. { eapply SessionPrelude.app_cancel_l with (prefix := take (uint.nat pos) l). rewrite take_drop. replace (uint.nat pos + 1)%nat with (S (uint.nat pos)) by word. rewrite take_drop_middle; trivial. } 
      iIntros "%s2 H_s2". iDestruct "H_s2" as "[[H1_s2 H2_s2] H3_s2]". wp_pures. wp_apply (wp_SliceTake); try word. wp_apply (wp_SliceAppendSlice with "[H_s1_prefix H3_s2 H1_s2 H2_s]"). { repeat econstructor; eauto. } { iFrame. iApply own_slice_cap_take; try word. iFrame. } iIntros "%s3 [H_s3 H1_s2]". wp_pures. iModIntro. iApply "HΦ". iSplitR "".
      - iDestruct "H_s3" as "[H1_s3 H2_s3]". pose proof (SessionPrelude.sortedInsert_unique (well_formed := Operation_wf n) l v claim2 claim3 (take (uint.nat pos) l) (drop (uint.nat pos) l) SORTED) as claim5. simpl in claim5. rewrite take_drop in claim5. specialize (claim5 eq_refl). change SessionPrelude.vectorEq with coq_equalSlices in *. change SessionPrelude.vectorGt with coq_lexicographicCompare in *. change SessionPrelude.sortedInsert with coq_sortedInsert in *. destruct (forallb _) as [ | ] eqn: H_forallb; rewrite SessionPrelude.forallb_spec in H_forallb.
        + assert (prefix' = take (uint.nat pos) ops) as ->.
          { rewrite H_ops. eapply SessionPrelude.list_ext.
            - rewrite length_take. rewrite length_app; simpl. word.
            - intros i x y [H_x H_y]. rewrite lookup_take in H_y; cycle 1. { rewrite <- H_len. eapply lookup_lt_is_Some_1. exists x; trivial. } rewrite lookup_app_l in H_y; cycle 1. { eapply lookup_lt_is_Some_1; trivial. } congruence.
          }
          assert (suffix' = drop (uint.nat pos + 1)%nat ops) as ->.
          { rewrite <- take_drop with (l := ops) (i := uint.nat pos) in H_ops at 1. apply SessionPrelude.app_cancel_l in H_ops. rewrite <- drop_drop. rewrite H_ops. reflexivity. }
          assert (drop (uint.nat pos) ops = o' :: drop (uint.nat pos + 1)%nat ops) as claim7.
          { eapply SessionPrelude.app_cancel_l with (prefix := take (uint.nat pos) ops). rewrite take_drop; trivial. }
          rewrite claim5.
          * iExists (take (uint.nat pos) ops ++ [o] ++ drop (uint.nat pos) ops). iFrame. iSplitL "H_prefix'".
            { iApply big_sepL2_flip. iFrame. }
            simpl. iSplitR "H_suffix' H_v'".
            { simpl. eauto. }
            { iApply big_sepL2_flip. rewrite claim7. rewrite claim6. simpl. iFrame. }
          * intros m y H_y. eapply PREFIX. pose proof (SessionPrelude.lookup_map getOperationVersionVector (take (uint.nat pos) l) m) as VIEW. rewrite H_y in VIEW. apply SessionPrelude.lookup_In in VIEW. rewrite SessionPrelude.map_take in VIEW. rewrite VECTOR in VIEW. rewrite take_app in VIEW. replace (take (uint.nat pos - length prefix) suffix) with ( @nil (list w64)) in VIEW; cycle 1. { symmetry. eapply nil_length_inv. rewrite length_take; word. } rewrite app_nil_r in VIEW. rewrite <- take_drop with (l := prefix) (i := uint.nat pos). rewrite in_app_iff. left; trivial.
          * intros m y H_y. eapply SUFFIX. pose proof (SessionPrelude.lookup_map getOperationVersionVector (drop (uint.nat pos) l) m) as VIEW. rewrite H_y in VIEW. apply SessionPrelude.lookup_In in VIEW. rewrite SessionPrelude.map_drop in VIEW. rewrite VECTOR in VIEW. rewrite drop_app in VIEW. replace (drop (uint.nat pos) prefix) with ( @nil (list w64)) in VIEW; cycle 1. { symmetry. eapply nil_length_inv. rewrite length_drop; word. } rewrite app_nil_l in VIEW. rewrite <- take_drop with (l := suffix) (i := (uint.nat pos - length prefix)%nat). rewrite in_app_iff. right; trivial.
        + assert (Operation_wf n v') as H_WF.
          { eapply List.Forall_forall with (l := l); trivial. rewrite <- take_drop with (l := l) (i := uint.nat pos). rewrite in_app_iff. right. rewrite claim6. simpl. left. trivial. }
          enough (v.(Operation.VersionVector) = v'.(Operation.VersionVector)) as H_v_v'. { rewrite H_v_v' in H_r. rewrite -> aux3_equalSlices in H_r. congruence. } pose proof (SessionPrelude.lookup_map getOperationVersionVector l (uint.nat pos)) as VIEW. rewrite LOOKUP in VIEW.
          rewrite VECTOR in VIEW. rewrite lookup_app_r in VIEW; try word. replace (uint.nat pos - length prefix)%nat with 0%nat in VIEW by word. simpl in VIEW. unfold getOperationVersionVector in VIEW. congruence.
      - iPureIntro. change (SessionPrelude.isSorted (well_formed := Operation_wf n) (SessionPrelude.sortedInsert (well_formed := Operation_wf n) l v)). eapply SessionPrelude.sortedInsert_isSorted; trivial.
    }
  Qed.

End heap.

#[global] Opaque CoqSessionServer.binarySearch.
#[global] Opaque CoqSessionServer.sortedInsert.
