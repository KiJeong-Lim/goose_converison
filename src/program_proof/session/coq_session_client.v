From Perennial.program_proof.session Require Export session_prelude definitions coq_session.

Definition Ev : Z := 0.
Definition Wfr : Z := 1.
Definition Mw : Z := 2.
Definition Mr : Z := 3.
Definition Ryw : Z := 4.
Definition Ca : Z := 5.

Module CoqSessionClient.

  Include Goose.github_com.session.client.

  Definition coq_read (c: Client.t) (serverId: u64) : Message.t :=
    match uint.Z c.(Client.SessionSemantic) with
    | 0 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 1 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 2 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 3 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 4 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (c.(Client.WriteVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 5 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | _ => Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    end.

  Definition coq_write (c: Client.t) (serverId: u64) (value: u64) : Message.t :=
    match uint.Z c.(Client.SessionSemantic) with
    | 0 => Message.mk 0 (c.(Client.Id)) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 1 => Message.mk 0 (c.(Client.Id)) serverId 1 value (c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 2 => Message.mk 0 (c.(Client.Id)) serverId 1 value (c.(Client.WriteVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 3 => Message.mk 0 (c.(Client.Id)) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 4 => Message.mk 0 (c.(Client.Id)) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 5 => Message.mk 0 (c.(Client.Id)) serverId 1 value (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | _ => Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    end.

  Definition coq_processRequest (c: Client.t) (requestType: u64) (serverId: u64) (value: u64) (ackMessage: Message.t) : Client.t * Message.t :=
    match uint.Z requestType with
    | 0 => (c, coq_read c serverId)
    | 1 => (c, coq_write c serverId value)
    | 2 =>
      match uint.Z ackMessage.(Message.S2C_Client_OperationType) with
      | 0 => (Client.mk c.(Client.Id) c.(Client.NumberOfServers) c.(Client.WriteVersionVector) ackMessage.(Message.S2C_Client_VersionVector) c.(Client.SessionSemantic), Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
      | 1 => (Client.mk c.(Client.Id) c.(Client.NumberOfServers) (ackMessage.(Message.S2C_Client_VersionVector)) c.(Client.ReadVersionVector) c.(Client.SessionSemantic), Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
      | _ => (c, Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
      end
    | _ => (c, Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
    end.

End CoqSessionClient.

Export CoqSessionClient.

Section heap.

  Context `{hG: !heapGS Σ}.

  Lemma wp_maxTwoInts (x: w64) (y: w64) :
    {{{
        True
    }}}
      CoqSessionClient.maxTwoInts #x #y 
    {{{
        r , RET #r;
        ⌜r = coq_maxTwoInts x y⌝
    }}}.
  Proof.
    iIntros (Φ) "H H1".
    rewrite /maxTwoInts. wp_pures.
    wp_if_destruct.
    - iModIntro. iApply "H1". iPureIntro.
      unfold coq_maxTwoInts. apply Z.gtb_lt in Heqb.
      rewrite Heqb. auto.
    - iModIntro. iApply "H1". iPureIntro.
      rewrite /coq_maxTwoInts.
      assert (uint.Z y >= uint.Z x) by word.
      assert (uint.Z x >? uint.Z y = false) by word.
      rewrite H0.
      auto.
  Qed.

  Lemma wp_maxTS (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) (d: dfrac) (d': dfrac) :
    {{{
        own_slice_small x uint64T d xs ∗
        own_slice_small y uint64T d' ys ∗
        ⌜length xs = length ys⌝
    }}}
      CoqSessionClient.maxTS x y 
    {{{
        (s': Slice.t), RET slice_val s'; 
        own_slice s' uint64T (DfracOwn 1) (coq_maxTS xs ys) ∗ 
        own_slice_small x uint64T d xs ∗
        own_slice_small y uint64T d' ys 
    }}}.
  Proof.
    iIntros (Φ) "(H & H1 & %H3) H2".
    rewrite /maxTS.
    iDestruct (own_slice_small_sz with "H") as %Hsz_x.
    iDestruct (own_slice_small_sz with "H1") as %Hsz_y.
    wp_pures. wp_apply wp_ref_to; auto.
    iIntros (index) "index". wp_pures.
    wp_pures. wp_apply wp_slice_len.
    wp_apply wp_ref_to; auto.
    iIntros (len) "len". wp_pures.
    wp_bind (NewSlice uint64T (slice.len x)).
    wp_apply wp_slice_len.
    wp_apply wp_new_slice; auto.
    iIntros (s') "s'". 
    wp_apply wp_ref_to; auto.
    iIntros (slice) "slice". wp_pures.
    wp_apply (wp_forBreak_cond
                (λ continue, ∃ (i: w64) (l: list w64),
                    own_slice_small x uint64T d xs ∗
                    own_slice_small y uint64T d' ys ∗
                    own_slice s' uint64T (DfracOwn 1) l ∗ 
                    index ↦[uint64T] #i ∗
                    len ↦[uint64T] #(length xs) ∗
                    slice ↦[slice.T uint64T] s' ∗ 
                    ⌜continue = false -> uint.nat i = (length xs)⌝ ∗
                    ⌜length l = length xs⌝ ∗
                    ⌜forall (i': nat),
                  i' < uint.nat i <= length xs ->
                  forall (x y: w64), xs !! i' = Some x ->
                                      ys !! i' = Some y ->
                                      l !! i' = Some (coq_maxTwoInts x y)⌝ ∗
                                      ⌜uint.nat i <= length xs⌝ 
                )%I
              with "[] [H H1 index len s' slice]").
    - iIntros (?). iModIntro. iIntros "H1 H2".
      iNamed "H1". iDestruct "H1"
        as "(Hx & Hy & H4 & H5 & H6 & H7 & %H8 & %H9 & %H10 & %H11)".
      wp_pures. wp_load. wp_load. wp_if_destruct.
      + wp_pures. wp_load.
        wp_bind (maxTwoInts _ _)%E.
        iDestruct "H4" as "[Hs Hsc]".
        assert (uint.nat i < length xs)%nat by word.
        rewrite H3 in H. eapply list_lookup_lt in H.
        destruct H as [x0 H].
        assert (uint.nat i < length xs)%nat by word.
        eapply list_lookup_lt in H0.
        destruct H0 as [y0 H0].
        wp_apply (wp_SliceGet with "[$Hy]"). { auto. }
        iIntros "Hy". wp_load. wp_apply (wp_SliceGet with "[$Hx]"). { auto. }
        iIntros "Hx".
        wp_apply (wp_maxTwoInts). iIntros (r) "%H12".
        wp_load. wp_load.
        wp_apply (wp_SliceSet with "[$Hs]").
        { iPureIntro. eapply lookup_lt_is_Some_2. word. }
        iIntros "H11". wp_pures. wp_load. wp_store. iModIntro.
        iApply "H2". iExists (w64_word_instance.(word.add) i (W64 1)).
        iExists (<[uint.nat i:=r]> l)%E. iFrame.
        iSplit. { auto. }
        iSplit. { iPureIntro. rewrite <- H9. apply length_insert. }
        iSplit. { iPureIntro. intros. destruct (decide (i' = uint.nat i)).
                  - rewrite list_lookup_insert_Some.
                    left.
                    split. { auto. }
                    split. { subst. rewrite H4 in H. rewrite H2 in H0. inversion H. inversion H0.
                            auto. }
                    word.
                  - rewrite Z.lt_le_pred in H1.
                    assert ((Z.pred (uint.nat (w64_word_instance.(word.add) i (W64 1)))) = uint.nat i) by word.
                    rewrite H5 in H1.
                    destruct H1. assert(uint.nat i ≠ i') by word.
                    apply (list_lookup_insert_ne l (uint.nat i) (i') r) in H7.
                    rewrite H7. eapply H10; try eassumption.
                    word.
        }
        word.
      + iModIntro. iApply "H2". iExists i. iExists l. iFrame. iPureIntro. split; auto. word.
    - assert (zero_val uint64T = #(W64 0)). { unfold zero_val. simpl. auto. }
      rewrite H. iExists (W64 0).
      iExists (replicate (uint.nat x.(Slice.sz)) (W64 0))%V.
      iFrame.
      iSplitL "s'". { rewrite /own_slice. rewrite untype_replicate. iFrame. }
      iSplitL "len". { rewrite Hsz_x.
                      assert (#(W64 (uint.nat x.(Slice.sz))) = #x.(Slice.sz)). {
                        f_equal. rewrite w64_to_nat_id. auto. }
                      rewrite H0. iFrame. }
      iPureIntro.
      split. { intros. inversion H0. }
      split. { rewrite length_replicate. auto. }
      split. { intros. word. }
      word.
    - iIntros "H". wp_pures. iNamed "H". iDestruct "H" as "(H1 & H3 & H4 & H5 & H6 & H7 & %H8 & %H9 & %H10 & %H11)".
      wp_load. iModIntro. iApply "H2". iFrame.
      assert (coq_maxTS xs ys = l). {
        clear Hsz_x.
        clear Hsz_y.        
        generalize dependent ys. generalize dependent l. generalize dependent i.
        induction xs.
        + intros. inversion H9. apply nil_length_inv in H0. rewrite H0. auto.
        + induction ys.
          * intros. inversion H3.
          * clear IHys. intros.
            assert (uint.nat (uint.nat i - 1%nat)%nat = ((uint.nat i) - 1)%nat) by word.
            destruct (decide (uint.Z a >? uint.Z a0 = true)).
            { inversion H3.
              assert (0%nat < uint.nat i <= length (a :: xs)). {
                destruct H8; auto. rewrite H3. repeat rewrite length_cons. word. }
              rewrite /coq_maxTS. rewrite /coq_maxTwoInts.
              rewrite e.
              eapply H10 in H0.
              - rewrite <- head_lookup in H0. rewrite head_Some in H0. destruct H0 as [l' H0].
                rewrite H0. f_equal.
                + assert (a = coq_maxTwoInts a a0). { rewrite /coq_maxTwoInts. rewrite e. auto. }
                  eassumption.
                + eapply IHxs.
                  * intros. destruct H8; auto.
                    rewrite length_cons in H3. assert (uint.nat (uint.nat i - 1)%nat = length xs) by word.
                    eassumption.
                  * rewrite H. rewrite length_cons in H11. word.
                  * rewrite length_cons in H9.
                    assert (length l = (1 + length l')%nat). { rewrite H0. simpl. auto. }
                    rewrite H9 in H2. word.
                  * auto.
                  * intros. assert (l !! (S i')%nat = l' !! i'). {
                      rewrite H0. rewrite lookup_cons.
                      auto. }
                    rewrite <- H6.
                    eapply H10.
                    { rewrite length_cons. word. }
                    { rewrite lookup_cons_Some. right. split.
                      - word.
                      - simpl. replace (i' - 0)%nat with i' by word. eassumption.
                    }
                    { rewrite lookup_cons_Some. right. split.
                      - word.
                      - simpl. replace (i' - 0)%nat with i' by word. eassumption.
                    }
              - auto.
              - auto.
            } 
            assert (uint.Z a >? uint.Z a0 = false) by word.
            rewrite /coq_maxTS. assert (a0 = coq_maxTwoInts a a0). { rewrite /coq_maxTwoInts. rewrite H0. auto. }
            rewrite <- H1.
            assert (0%nat < uint.nat i <= length (a :: xs)). {
              destruct H8; auto. rewrite H3. repeat rewrite length_cons. word. }
            eapply H10 in H2.
            { rewrite <- head_lookup in H2. rewrite head_Some in H2. destruct H2 as [l' H2].
              rewrite H2. f_equal.
              - eassumption.
              - eapply IHxs.
                + intros.
                  inversion H3.
                  destruct H8; auto.
                  rewrite length_cons in H3.
                  assert (uint.nat (uint.nat i - 1)%nat = length xs) by word.
                  eassumption.
                + rewrite H. rewrite length_cons in H11. word.
                + rewrite length_cons in H9.
                  assert (length l = (1 + length l')%nat). {  rewrite H2. simpl. auto. }
                  rewrite H9 in H4. word.
                + auto.
                + intros.
                  assert (l !! (S i')%nat = l' !! i').
                  { rewrite H2. rewrite lookup_cons.
                    auto. }
                  rewrite <- H7.
                  eapply H10.
                  * rewrite length_cons. word. 
                  * rewrite lookup_cons_Some. right. split.
                    { word. }
                    { simpl. replace (i' - 0)%nat with i' by word. eassumption. }
                  * rewrite lookup_cons_Some. right. split.
                      { word. }
                      { simpl. replace (i' - 0)%nat with i' by word. eassumption. }
            }
        - auto.
        - auto.
      }
      rewrite H. iFrame.
  Qed.

  Lemma wp_read (c: Client.t) (serverId: u64) (n: nat) cv :
    {{{
        is_client cv c n ∗
        ⌜n = uint.nat c.(Client.NumberOfServers)⌝
    }}}
      CoqSessionClient.read (client_val cv) (#serverId)
    {{{
        msgv, RET (message_val msgv);
        is_client cv c n ∗
        is_message msgv (coq_read c serverId) n n 0%nat
    }}}.
  Proof. (**
    rewrite redefine_client_val redefine_message_val. TypeVector.des cv. iIntros "%Φ (H_is_client & ->) HΦ".
    iDestruct "H_is_client" as "(%H1 & %H2 & H3 & %H4 & H5 & %H6 & %H7)".
    simplNotation; simpl; subst; rewrite /CoqSessionClient.read.
    iPoseProof (own_slice_small_sz with "[$H3]") as "%LENGTH1".
    iPoseProof (own_slice_small_sz with "[$H5]") as "%LENGTH2".
    wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%reply H_reply".
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 0))) as [ | ] eqn: Heqb.
    { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
      iPoseProof (own_slice_sz with "[$H_s1]") as "%LENGTH3". rewrite length_replicate in LENGTH3.
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_load.
      apply bool_decide_eq_true in Heqb.
      assert (c .(Client.SessionSemantic) = W64 0) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_read. rewrite -> EQ. replace (uint.Z (W64 0)) with 0%Z by word.
        unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
        iSplitL "". { rewrite length_replicate. done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply own_slice_small_nil; eauto. }
        iSplitL "". { iPureIntro. word. }
        done.
    }
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 1))) as [ | ] eqn: Heqb0.
    { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
      iPoseProof (own_slice_sz with "[$H_s1]") as "%LENGTH3". rewrite length_replicate in LENGTH3.
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_load.
      apply bool_decide_eq_true in Heqb0.
      assert (c .(Client.SessionSemantic) = W64 1) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_read. rewrite -> EQ. replace (uint.Z (W64 1)) with 1%Z by word.
        unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
        iSplitL "". { rewrite length_replicate. done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply own_slice_small_nil; eauto. }
        iSplitL "". { iPureIntro. word. }
        done.
    }
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 2))) as [ | ] eqn: Heqb1.
    { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
      iPoseProof (own_slice_sz with "[$H_s1]") as "%LENGTH3". rewrite length_replicate in LENGTH3.
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_load.
      apply bool_decide_eq_true in Heqb1.
      assert (c .(Client.SessionSemantic) = W64 2) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_read. rewrite -> EQ. replace (uint.Z (W64 2)) with 2%Z by word.
        unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
        iSplitL "". { rewrite length_replicate. done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply own_slice_small_nil; eauto. }
        iSplitL "". { iPureIntro. word. }
        done.
    }
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 3))) as [ | ] eqn: Heqb2.
    { admit. }
    admit.
  Qed. *) Admitted.

  Lemma wp_write (c: Client.t) (serverId: u64) (value: u64) (n: nat) cv :
    {{{
        is_client cv c n ∗
        ⌜n = uint.nat c.(Client.NumberOfServers)⌝
    }}}
      CoqSessionClient.write (client_val cv) (#serverId) (#value)
    {{{
        msgv, RET (message_val msgv);
        is_client cv c n ∗
        is_message msgv (coq_write c serverId value) n n 0%nat
    }}}.
  Proof.
  Admitted.

  Lemma wp_processRequest (c: Client.t) (requestType: u64) (serverId: u64) (value: u64) (ackMessage: Message.t) (n: nat) cv msgv :
    {{{
        is_client cv c n ∗
        is_message msgv ackMessage n n n ∗
        ⌜n = uint.nat c.(Client.NumberOfServers)⌝
    }}}
      CoqSessionClient.processRequest (client_val cv) (#requestType) (#serverId) (#value) (message_val msgv)
    {{{
        cv' msgv', RET (client_val cv', message_val msgv');
        is_client cv' (coq_processRequest c requestType serverId value ackMessage).1 n ∗
        ∃ n', is_message msgv' (coq_processRequest c requestType serverId value ackMessage).2 n n' 0%nat ∗
        is_message msgv ackMessage n n n ∗
        ⌜n = uint.nat (coq_processRequest c requestType serverId value ackMessage).1.(Client.NumberOfServers)⌝
    }}}.
  Proof.
  Admitted.

End heap.
