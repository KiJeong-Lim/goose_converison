From Perennial.program_proof.session Require Export session_prelude.
From Perennial.program_proof.session Require Export coq_session.
From Perennial.program_proof.session Require Export versionVector.

Section heap.
  Context `{hG: !heapGS Σ}.

  Variant binarySearch_spec (needle: Operation.t) (l: list Operation.t) (n: nat) (r: nat) : Prop :=
    | binarySearch_spec_intro prefix suffix
      (LENGTH: r = length prefix)
      (CONCAT: l = if forallb (fun x => negb (coq_equalSlices x.(Operation.VersionVector) needle.(Operation.VersionVector))) l then prefix ++ suffix else prefix ++ [needle] ++ suffix)
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
    { admit. }
    { admit. }
  Admitted.

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
