From Perennial.program_proof.session Require Export session_prelude coq_session.
From Perennial.program_proof.session Require Export versionVector sort.

Section heap.

  Context `{hG: !heapGS Σ}.

  Lemma wp_deleteAtIndexOperation (s: Slice.t) (index: w64) (l: list Operation.t) (n: nat) :
    {{{
        operation_slice s l n ∗
        ⌜(uint.nat index < length l)%nat⌝
    }}}
      CoqSessionServer.deleteAtIndexOperation s #index
    {{{
        ns, RET (slice_val ns);
        operation_slice ns (coq_deleteAtIndexOperation l (uint.nat index)) n ∗
        ⌜(length (coq_deleteAtIndexOperation l (uint.nat index)) + 1 = length l)%nat⌝
    }}}.
  Proof.
    rewrite/ deleteAtIndexOperation. rename s into s1. iIntros (Φ) "[(%ops1 & H_s1 & H_ops1) %H_index] HΦ".
    iPoseProof (big_sepL2_length with "[$H_ops1]") as "%claim1".
    iPoseProof (own_slice_sz with "[$H_s1]") as "%claim2".
    wp_pures. wp_apply wp_NewSlice. iIntros "%s2 H_s2". wp_apply wp_ref_to; auto.
    iIntros "%ret H_ret". wp_pures.
    iAssert ⌜uint.Z index ≤ uint.Z s1 .(Slice.cap)⌝%I as "%H_s_cap".
    { iPoseProof (own_slice_wf with "[$H_s1]") as "%claim3".
      iPoseProof (big_sepL2_length with "[$H_ops1]") as "%claim4".
      iPoseProof (own_slice_sz with "[$H_s1]") as "%claim5".
      iPureIntro. word.
    }
    iPoseProof (own_slice_cap_wf with "[H_s1]") as "%claim3".
    { iDestruct "H_s1" as "[H1_s1 H2_s1]". iFrame. }
    iAssert ⌜uint.Z index ≤ length ops1⌝%I as "%H_ops1_len".
    { iPureIntro. word. }
    wp_apply (wp_SliceTake with "[H_s1 H_s2 H_ops1 H_ret HΦ]"); eauto.
    iModIntro. wp_load.
    iPoseProof (slice_small_split _ _ _ _ _ H_ops1_len with "[H_s1]") as "[H_s1_prefix H_s1_suffix]".
    { iApply (own_slice_to_small with "[$H_s1]"). }
    wp_apply (wp_SliceAppendSlice with "[H_s2 H_s1_prefix]"); eauto.
    { iFrame. }
    iIntros "%s3 [H_s3 H_s1_prefix]". simpl in *. replace (replicate (uint.nat (W64 0)) (Slice.nil, W64 0)) with (nil (A := Slice.t * w64)) by reflexivity.
    simpl. wp_store. wp_pures.
    iPoseProof (own_slice_small_sz with "[$H_s1_prefix]") as "%claim4".
    iPoseProof (own_slice_small_sz with "[$H_s1_suffix]") as "%claim5".
    iDestruct "H_s3" as "[H1_s3 H2_s3]".
    iPoseProof (own_slice_cap_wf with "[H2_s3]") as "%claim6".
    { unfold own_slice. unfold slice.own_slice. iFrame. }
    iAssert ⌜uint.Z (w64_word_instance .(word.add) index (W64 1)) ≤ uint.Z s1 .(Slice.sz)⌝%I as "%claim7".
    { iPureIntro. word. }
    wp_apply (wp_SliceSkip); eauto.
    wp_load. wp_apply (wp_SliceAppendSlice with "[H1_s3 H2_s3 H_s1_suffix]"); eauto.
    { iSplitR "H_s1_suffix".
      - iApply own_slice_split. iFrame.
      - iPoseProof (own_slice_small_take_drop with "[$H_s1_suffix]") as "[H_s1_suffix_hd H_s1_suffix_tl]".
        { instantiate (1 := W64 1). rewrite length_drop in claim5. rewrite length_take in claim4. word. }
        instantiate (2 := DfracOwn 1). instantiate (1 := (drop (uint.nat (W64 1)) (drop (uint.nat index) ops1))).
        erewrite slice_skip_skip with (n := w64_word_instance .(word.add) index (W64 1)) (m := index) (s := s1); simpl.
        + replace (w64_word_instance .(word.sub) (w64_word_instance .(word.add) index (W64 1)) index) with (W64 1) by word. iFrame.
        + word.
        + word.
    }
    iIntros "%s4 [H1_s4 H2_s4]". iApply "HΦ". simpl.
    replace (coq_deleteAtIndexOperation l (uint.nat index)) with (take (uint.nat index) l ++ drop (uint.nat (W64 1)) (drop (uint.nat index) l)).
    - iSplitR "".
      + iExists ((take (uint.nat index) ops1 ++ drop (uint.nat (W64 1)) (drop (uint.nat index) ops1)))%list. iSplitR "H_ops1".
        * iFrame.
        * iPoseProof (big_sepL2_app_equiv with "[H_ops1]") as "[H_prefix H_suffix]".
          { instantiate (1 := take (uint.nat index) l). instantiate (1 := take (uint.nat index) ops1).
            rewrite length_take. rewrite length_take. word.
          }
          { instantiate (2 := drop (uint.nat index) ops1). instantiate (1 := drop (uint.nat index) l).
            rewrite take_drop. rewrite take_drop. iExact "H_ops1".
          }
          simpl. iApply (big_sepL2_app with "[H_prefix]"). { iExact "H_prefix". }
          destruct (drop (uint.nat index) ops1) as [ | ops1_hd ops1_tl] eqn: H_ops1.
          { simpl in *. iPoseProof (big_sepL2_nil_inv_l with "[$H_suffix]") as "%NIL".
            rewrite NIL. iExact "H_suffix".
          }
          iPoseProof (big_sepL2_cons_inv_l with "[$H_suffix]") as "(%l_hd & %l_tl & %H_l & H_hd & H_tl)".
          rewrite H_l. iExact "H_tl".
      + iPureIntro. rewrite length_app. rewrite length_take. rewrite length_drop. rewrite length_drop. word.
    - unfold coq_deleteAtIndexOperation. replace (drop (uint.nat index + 1) l) with (drop (uint.nat (W64 1)) (drop (uint.nat index) l)); trivial.
      rewrite drop_drop. f_equal.
  Qed.

  Lemma wp_deleteAtIndexMessage (s: Slice.t) (index: w64) (l: list Message.t) (n: nat) (len_c2s: nat) :
    {{{ 
        message_slice s l n len_c2s ∗
        ⌜(uint.nat index < length l)%nat⌝
    }}}
      CoqSessionServer.deleteAtIndexMessage s #index
    {{{
        ns, RET (slice_val ns);
        message_slice ns (coq_deleteAtIndexMessage l (uint.nat index)) n len_c2s ∗
        ⌜(length (coq_deleteAtIndexMessage l (uint.nat index)) + 1 = length l)%nat⌝
    }}}.
  Proof.
    rewrite/ deleteAtIndexMessage. rename s into s1. iIntros (Φ) "[(%ops1 & H_s1 & H_ops1) %H_index] HΦ".
    iPoseProof (big_sepL2_length with "[$H_ops1]") as "%claim1".
    iPoseProof (own_slice_sz with "[$H_s1]") as "%claim2".
    wp_pures. wp_apply wp_NewSlice. iIntros "%s2 H_s2". wp_apply wp_ref_to; auto.
    iIntros "%ret H_ret". wp_pures.
    iAssert ⌜uint.Z index ≤ uint.Z s1 .(Slice.cap)⌝%I as "%H_s_cap".
    { iPoseProof (own_slice_wf with "[$H_s1]") as "%claim3".
      iPoseProof (big_sepL2_length with "[$H_ops1]") as "%claim4".
      iPoseProof (own_slice_sz with "[$H_s1]") as "%claim5".
      iPureIntro. word.
    }
    iPoseProof (own_slice_cap_wf with "[H_s1]") as "%claim3".
    { iDestruct "H_s1" as "[H1_s1 H2_s1]". iFrame. }
    iAssert ⌜uint.Z index ≤ length ops1⌝%I as "%H_ops1_len".
    { iPureIntro. word. }
    wp_apply (wp_SliceTake with "[H_s1 H_s2 H_ops1 H_ret HΦ]"); eauto.
    iModIntro. wp_load.
    iAssert ⌜uint.Z (w64_word_instance .(word.add) index (W64 1)) ≤ length ops1⌝%I as "%YES". { word. }
    iPoseProof (slice_small_split _ _ _ _ _ YES with "[H_s1]") as "[H1_s1 H3_s1]".
    { iApply (own_slice_to_small with "[$H_s1]"). }
    assert (forall A : Type, forall x : A, replicate (uint.nat (W64 0)) x = []) as YES1 by reflexivity.
    rewrite YES1. simpl. clear YES1.
    assert (uint.Z index ≤ length (take (uint.nat (w64_word_instance .(word.add) index (W64 1))) ops1)) as YES2. { rewrite length_take. word. }
    iPoseProof (slice_small_split _ _ _ _ _ YES2 with "[$H1_s1]") as "[H1_s1 H2_s1]".
    wp_apply (wp_SliceAppendSlice with "[H_s2 H1_s1]"); eauto.
    { done. } { iFrame. } iIntros "%s' [H1_s' H2_s']". wp_pures. wp_store.
    wp_apply (wp_SliceSkip); eauto. { word. } wp_load. wp_apply (wp_SliceAppendSlice with "[H1_s' H3_s1]"). { done. }
    { simpl in *. iFrame. } iIntros "%s'' [H1_s'' H2_s'']". iApply "HΦ".
    unfold message_slice. iSplitR "".
    - iExists (take (uint.nat index) ops1 ++ drop (uint.nat index + 1)%nat ops1). iSplitR "H_ops1".
      + remember (uint.nat index) as k eqn: H_k in *.
        replace (uint.nat (w64_word_instance .(word.add) index (W64 1))) with (k + 1)%nat in * by word.
        rewrite take_take. replace (k `min` (k + 1))%nat with k by word. iFrame.
      + unfold coq_deleteAtIndexMessage. iPoseProof (big_sepL2_length with "[$H_ops1]") as "%YES1".
        iApply big_sepL2_app_equiv. { do 2 rewrite length_take; word. }
        rewrite <- take_drop with (l := ops1) (i := uint.nat index) at 1.
        rewrite <- take_drop with (l := l) (i := uint.nat index) at 1.
        iAssert (([∗ list] mv;m ∈ take (uint.nat index) ops1;take (uint.nat index) l, ∃ b, is_message mv m n len_c2s b) ∗ ([∗ list] mv;m ∈ drop (uint.nat index) ops1;drop (uint.nat index) l, ∃ b, is_message mv m n len_c2s b))%I with "[H_ops1]" as "[H_prefix H_suffix]".
        { iApply (big_sepL2_app_equiv with "[$H_ops1]"). do 2 rewrite length_take. word. }
        iFrame. destruct (drop (uint.nat index) ops1) as [ | hd tl] eqn: H_obs.
        * iPoseProof (big_sepL2_nil_inv_l with "[$H_suffix]") as "%H_obs'".
          do 2 rewrite <- drop_drop. rewrite H_obs H_obs'. simpl. done.
        * iPoseProof (big_sepL2_cons_inv_l with "[$H_suffix]") as "(%hd' & %tl' & %H_obs' & H1 & H2)".
          do 2 rewrite <- drop_drop. rewrite H_obs H_obs'. simpl. done.
    - iPureIntro. rewrite length_app. rewrite length_take. rewrite length_drop. word.
  Qed.

  Lemma wp_getDataFromOperationLog (s: Slice.t) (l: list Operation.t) (n: nat) :
    {{{
        operation_slice s l n
    }}}
      CoqSessionServer.getDataFromOperationLog s
    {{{
        r, RET #r;
        ⌜r = coq_getDataFromOperationLog l⌝ ∗
        operation_slice s l n
    }}}.
  Proof.
    rewrite/ getDataFromOperationLog. wp_pures. iIntros "%Φ Hl H1". wp_pures.
    wp_rec. iDestruct "Hl" as "(%ops & Hs & Hl)". iPoseProof (pers_big_sepL2_is_operation with "[$Hl]") as "#Hl_pers". wp_if_destruct.
    - wp_rec.
      iAssert (⌜is_Some (ops !! uint.nat (w64_word_instance .(word.sub) s .(Slice.sz) (W64 1)))⌝%I) with "[Hl Hs]" as "%Hl".
      { induction ops as [ | ? ? _] using List.rev_ind.
        - iAssert (⌜l = []⌝)%I with "[Hl]" as "%Hl".
          { iApply big_sepL2_nil_inv_l. iExact "Hl". }
          subst l. simpl. iPoseProof (own_slice_sz with "[$Hs]") as "%Hs".
          simpl in *. iPureIntro. word.
        - iPoseProof (own_slice_sz with "[$Hs]") as "%Hs".
          iPureIntro. red. exists x. eapply list_lookup_middle. rewrite length_app in Hs. simpl in Hs. word.
      }
      iAssert (⌜length ops = length l⌝)%I with "[Hl]" as "%Hlength".
      { iApply big_sepL2_length. iExact "Hl". }
      destruct Hl as (x & EQ). iDestruct "Hs" as "[H1s H2s]".
      wp_apply (wp_SliceGet with "[H1s] [Hl H1 H2s]").
      + iSplitL "H1s".
        * simpl (struct.t Operation). iExact "H1s".
        * iPureIntro. exact EQ.
      + iModIntro. iIntros "Hs".
        wp_pures. iModIntro. iApply "H1".
        unfold coq_getDataFromOperationLog.
        iPoseProof (own_slice_small_sz with "[$Hs]") as "%Hs".
        induction ops as [ | ops_last ops_init _] using List.rev_ind.
        { simpl in *. word. }
        induction l as [ | l_last l_init _] using List.rev_ind.
        { simpl in *. word. }
        iPoseProof big_sepL2_snoc as "LEMMA1". iApply "LEMMA1" in "Hl". iClear "LEMMA1".
        iDestruct "Hl" as "[H_init H_last]". rewrite last_app; simpl. rewrite length_app in Hs. simpl in *.
        iPoseProof (big_sepL2_length with "[$H_init]") as "%YES".
        replace (uint.nat (W64 ((length l_init + 1)%nat - 1))) with (length l_init) by (simpl; word).
        replace (uint.nat (W64 (length l_init + 1 - 1)%nat)) with (length l_init) by word.
        change (list_lookup (length l_init) (l_init ++ [l_last])) with ((l_init ++ [l_last]) !! (length l_init)).
        replace (uint.nat (w64_word_instance .(word.sub) s .(Slice.sz) (W64 1))) with (length ops_init) in EQ by word.
        rewrite lookup_snoc in EQ. assert (x = ops_last) as -> by congruence. clear EQ.
        iDestruct "H_last" as "[H [-> H1]]". iFrame. iExact "Hl_pers".
    - iModIntro. iApply "H1". unfold coq_getDataFromOperationLog.
      iAssert (⌜uint.Z (W64 0) = uint.Z s .(Slice.sz)⌝)%I as "%NIL".
      { word. }
      destruct l as [ | ? ?].
      { simpl. iFrame. iPureIntro. done. }
      simpl. destruct ops as [ | ? ?].
      { iPoseProof (big_sepL2_nil_inv_l with "[$Hl]") as "%Hl". congruence. }
      iPoseProof (own_slice_sz with "[$Hs]") as "%Hs".
      simpl in Hs. word.
  Qed.

  Lemma wp_receiveGossip sv s msgv msg (n: nat) len_c2s len_s2c len_mo len_ga Id NumberOfServers UnsatisfiedRequests MyOperations GossipAcknowledgements :
    {{{
        is_server sv s n n n len_mo n len_ga ∗ 
        is_message msgv msg n len_c2s len_s2c ∗
        ⌜WEAK_SERVER_INVARIANT (fun _s => _s.(Server.Id) = Id /\ _s.(Server.NumberOfServers) = NumberOfServers /\ _s.(Server.UnsatisfiedRequests) = UnsatisfiedRequests /\ _s.(Server.MyOperations) = MyOperations /\ _s.(Server.GossipAcknowledgements) = GossipAcknowledgements) s⌝
    }}}
      CoqSessionServer.receiveGossip (server_val sv) (message_val msgv)
    {{{
        r, RET (server_val r);
        is_server r (coq_receiveGossip s msg) n n n len_mo n len_ga ∗
        is_message msgv msg n len_c2s len_s2c ∗
        ⌜WEAK_SERVER_INVARIANT (fun _s => _s.(Server.Id) = Id /\ _s.(Server.NumberOfServers) = NumberOfServers /\ _s.(Server.UnsatisfiedRequests) = UnsatisfiedRequests /\ _s.(Server.MyOperations) = MyOperations /\ _s.(Server.GossipAcknowledgements) = GossipAcknowledgements) (coq_receiveGossip s msg)⌝
    }}}.
  Proof.
    (* rewrite redefine_server_val redefine_message_val. TypeVector.des sv. TypeVector.des msgv.
    iIntros "%Φ (H_server & H_message & [%H1_sorted %H2_sorted]) HΦ". rewrite /acknowledgeGossip.
    iDestruct "H_server" as "(%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10)".
    iDestruct "H_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & %H19 & H20 & %H21 & %H22 & %H23 & %H24 & %H25 & %H26 & H27 & %H28 & %H29 & %H30)".
    simplNotation. subst. rewrite /receiveGossip.
    wp_pures. wp_apply wp_slice_len. wp_if_destruct.
    - iModIntro. set (r := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)).
      replace (Φ (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #()))))))))%V) with (Φ (#r.1.1.1.1.1.1.1, (#r.1.1.1.1.1.1.2, (r.1.1.1.1.1.2, (r.1.1.1.1.2, (r.1.1.1.2, (r.1.1.2, (r.1.2, (r.2, #()))))))))%V) by f_equal.
      iApply "HΦ". simpl. unfold coq_receiveGossip.
      destruct (length msg .(Message.S2S_Gossip_Operations) =? 0) as [ | ] eqn: H_OBS.
      + rewrite Z.eqb_eq in H_OBS. simpl. subst r. iFrame. iPureIntro. done.
      + rewrite Z.eqb_neq in H_OBS. iDestruct "H20" as "(%ops & H1_20 & H2_20)".
        iPoseProof (own_slice_sz with "[$H1_20]") as "%YES1".
        iPoseProof (big_sepL2_length with "[$H2_20]") as "%YES2".
        word.
    - replace ((#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #())))))))))%V with ( @SessionPrelude.value_of (tuple_of[u64,u64,Slice.t,Slice.t,Slice.t,Slice.t,Slice.t,Slice.t]) _ (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)) by reflexivity. rewrite <- redefine_server_val. simplNotation.
      wp_apply wp_ref_to. { repeat econstructor; eauto. } rewrite redefine_server_val. simplNotation. iIntros "%server H_server".
      wp_pures. wp_load. wp_apply (wp_mergeOperations with "[$H8 $H20]"); auto. iIntros "%ns (%nxs & H31 & -> & H8 & H20 & %H2_sorted')".
      wp_apply (wp_storeField_struct with "[H_server]"). { repeat constructor; auto. } { iExact "H_server". }
      simpl. iIntros "H_server". wp_pures. wp_apply wp_ref_to; auto. iIntros "%i H_i". wp_pures.
      rename t4 into UnsatisfiedRequests, t3 into VectorClock, t2 into OperationsPerformed, t1 into MyOperations, t0 into PendingOperations, t into GossipAcknowledgements.
      set (focus := coq_mergeOperations s .(Server.PendingOperations) msg .(Message.S2S_Gossip_Operations)) in H2_sorted' |- *.
      set (loop_init := (0%nat, Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) focus s.(Server.GossipAcknowledgements))).
      set (loop_step := λ (acc : nat * Server.t) (e : Operation.t),
        let '(i, s) := acc in
        if coq_oneOffVersionVector s.(Server.VectorClock) e.(Operation.VersionVector) then
          let OperationsPerformed := coq_mergeOperations s.(Server.OperationsPerformed) [e] in
          let VectorClock := coq_maxTS s.(Server.VectorClock) e.(Operation.VersionVector) in
          let PendingOperations := coq_deleteAtIndexOperation s.(Server.PendingOperations) i in
          (i, Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed s.(Server.MyOperations) PendingOperations s.(Server.GossipAcknowledgements))
        else ((i + 1)%nat, s)
      ).
      set (n := length s .(Server.VectorClock)). rename s into s0.
      wp_apply (wp_forBreak_cond
        ( λ continue, ∃ prevs : list Operation.t, ∃ nexts : list Operation.t, ∃ index : nat, ∃ s : Server.t, ∃ UnsatisfiedRequests : Slice.t, ∃ VectorClock : Slice.t, ∃ OperationsPerformed : Slice.t, ∃ PendingOperations : Slice.t, ∃ GossipAcknowledgements : Slice.t,
          ⌜focus = prevs ++ nexts⌝ ∗
          ⌜(index, s) = fold_left loop_step prevs loop_init⌝ ∗
          i ↦[uint64T] #index ∗
          server ↦[struct.t Server] (#s .(Server.Id), (#s .(Server.NumberOfServers), (UnsatisfiedRequests, (VectorClock, (OperationsPerformed, (MyOperations, (PendingOperations, (GossipAcknowledgements, #())))))))) ∗
          message_slice UnsatisfiedRequests s .(Server.UnsatisfiedRequests) n n ∗
          own_slice_small VectorClock uint64T (DfracOwn 1) s .(Server.VectorClock) ∗
          operation_slice OperationsPerformed s .(Server.OperationsPerformed) n ∗
          operation_slice MyOperations s .(Server.MyOperations) len_mo ∗
          operation_slice PendingOperations s .(Server.PendingOperations) n ∗
          own_slice_small GossipAcknowledgements uint64T (DfracOwn 1) s .(Server.GossipAcknowledgements) ∗
          own_slice_small t7 uint64T (DfracOwn 1) msg .(Message.C2S_Client_VersionVector) ∗
          operation_slice t6 msg .(Message.S2S_Gossip_Operations) n ∗
          own_slice_small t5 uint64T (DfracOwn 1) msg .(Message.S2C_Client_VersionVector) ∗
          ⌜length s .(Server.PendingOperations) = (index + length nexts)%nat⌝ ∗
          ⌜drop index s .(Server.PendingOperations) = nexts⌝ ∗
          ⌜length s .(Server.VectorClock) = length s0 .(Server.VectorClock)⌝ ∗
          ⌜is_sorted (take index s .(Server.PendingOperations) ++ nexts) /\ is_sorted s .(Server.OperationsPerformed)⌝ ∗
          ⌜length s .(Server.GossipAcknowledgements) = length s0 .(Server.GossipAcknowledgements)⌝ ∗
          ⌜(index <= uint.nat PendingOperations .(Slice.sz))%nat⌝ ∗
          ⌜length s .(Server.PendingOperations) = uint.nat PendingOperations .(Slice.sz)⌝ ∗
          ⌜s .(Server.MyOperations) = s0 .(Server.MyOperations) /\ s .(Server.Id) = s0 .(Server.Id)⌝ ∗
          ⌜continue = false -> nexts = []⌝
        )%I
      with "[] [H_i H_server H3 H4 H6 H7 H8 H9 H16 H20 H27 H31]").
      { clear Φ UnsatisfiedRequests VectorClock OperationsPerformed PendingOperations GossipAcknowledgements.
        iIntros "%Φ". iModIntro. iIntros "(%prevs & %nexts & %index & %s & %UnsatisfiedRequests & %VectorClock & %OperationsPerformed & %PendingOperations & %GossipAcknowledgements & %H_split_focus & %H_loop & H_i & H_server & H3 & H4 & H6 & H7 & H8 & H20 & H9 & H16 & H27 & %H_length & %H_nexts & %H1_invariant & [%H2_invariant %H2_invariant'] & %H_index & %H3_invariant & %H4_invariant & [%H5_invariant %H6_invariant] & %H_continue) HΦ".
        wp_pures. wp_load. wp_load. wp_pures. wp_apply wp_slice_len. wp_if_destruct.
        - wp_pures. wp_load. wp_pures. wp_load. wp_pures. iDestruct "H8" as "(%ops1 & [H1_8 H2_8] & H3_8)".
          iPoseProof (big_sepL2_length with "[$H3_8]") as "%YES1".
          iPoseProof (own_slice_small_sz with "[$H1_8]") as "%YES2".
          assert (is_Some (ops1 !! uint.nat (W64 index))) as [e H_e].
          { eapply lookup_lt_is_Some_2. word. }
          assert (length nexts > 0)%nat as NE_NIL by word.
          destruct nexts as [ | cur nexts].
          { simpl in NE_NIL. word. }
          clear NE_NIL H_continue.
          assert (s .(Server.PendingOperations) !! index = Some cur) as H_cur.
          { rewrite <- take_drop with (l := s .(Server.PendingOperations)) (i := index). rewrite lookup_app_r.
            - rewrite H_nexts. replace (index - length (take index s .(Server.PendingOperations)))%nat with 0%nat.
              + reflexivity.
              + symmetry. rewrite length_take. word.
            - rewrite length_take. word.
          }
          wp_apply (wp_SliceGet with "[$H1_8]"); auto. iIntros "H1_8". wp_pures. wp_load. wp_pures.
          iPoseProof (pers_big_sepL2_is_operation with "[$H3_8]") as "#H3_8_pers".
          replace (uint.nat (W64 index)) with index in H_e by word.
          iPoseProof (big_sepL2_is_operation_elim with "[$H3_8_pers]") as "(%op2 & %H1_op2 & #H2_op2)"; eauto.
          iPoseProof (own_slice_small_sz with "[$H4]") as "%YES3".
          wp_apply (wp_oneOffVersionVector with "[$H4 $H2_op2]"). { iPureIntro. rewrite <- H1_op2. exact H1_invariant. }
          iIntros "%b (-> & H4 & H2_op2' & %H_length')". wp_if_destruct.
          + wp_pures. wp_load. wp_pures. wp_load. wp_pures. wp_apply (wp_SliceGet with "[$H1_8]"). { replace (uint.nat (W64 index)) with index by word. iPureIntro. exact H_e. }
            iIntros "H1_8". wp_apply (wp_SliceSingleton). iIntros "%s1 H_s1". wp_pures. wp_load. wp_pures.
            wp_apply (wp_mergeOperations with "[$H6 $H_s1]").
            { instantiate (1 := [cur]). iSplit.
              - simpl. iSplit; trivial. iApply (big_sepL2_is_operation_elim with "[$H3_8_pers]"); eauto.
              - iPureIntro. done.
            }
            iIntros "%ns' (%nxs & H_ns' & -> & H6 & H_s1 & %H3_sorted)".
            wp_apply (wp_storeField_struct with "[$H_server]"). { repeat econstructor; eauto. } iIntros "H_server".
            wp_load. wp_pures. wp_load. wp_apply (wp_SliceGet with "[$H1_8]"). { replace (uint.nat (W64 index)) with index by word. iPureIntro. exact H_e. }
            iIntros "H1_8". wp_pures. wp_load. wp_pures. wp_apply (wp_maxTS with "[$H4 $H2_op2]"). { eauto. }
            iIntros "%s2 (H_s2 & H4 & H2_ops')". wp_apply (wp_storeField_struct with "[$H_server]"). { repeat econstructor; eauto. }
            iIntros "H_server". wp_pures. wp_load. wp_load. wp_pures. wp_apply (wp_deleteAtIndexOperation with "[$H1_8 $H2_8 $H3_8]"). { iPureIntro. word. }
            iIntros "%ns2 [H_ns2 %LEN_ns2]". wp_apply (wp_storeField_struct with "[$H_server]"). { repeat econstructor; eauto. }
            iIntros "H_server". simpl in *. wp_pures. iModIntro. iApply "HΦ".
            iExists (prevs ++ [cur]). iExists nexts. iExists index. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _.
            iDestruct "H_ns2" as "(%ops & H_ops & H_ns2)".
            iPoseProof (big_sepL2_length with "[$H_ns2]") as "%claim1".
            iPoseProof (own_slice_sz with "[$H_ops]") as "%claim2".
            iSplitL "".
            { iPureIntro. rewrite <- app_assoc. simpl. exact H_split_focus. }
            iSplitL "".
            { iPureIntro. rewrite fold_left_app. simpl. unfold loop_step at 1. rewrite <- H_loop. simpl. rewrite Heqb1. reflexivity. }
            simpl. replace (uint.nat (W64 index)) with index by word. iFrame.
            iSplitL "H_s2". { iApply (own_slice_to_small with "[$H_s2]"). }
            iPureIntro.
            { unfold coq_deleteAtIndexOperation. split.
              - rewrite length_app length_take length_drop. word.
              - rewrite drop_app. replace (drop index (take index s .(Server.PendingOperations))) with ( @nil Operation.t); cycle 1.
                { symmetry. eapply nil_length_inv. rewrite length_drop length_take. word. }
                simpl. rewrite length_take.
                assert (index < length s .(Server.PendingOperations))%nat as YES4.
                { eapply lookup_lt_is_Some_1. done. }
                replace ((index - index `min` length s .(Server.PendingOperations)))%nat with 0%nat by word.
                replace (drop 0 (drop (index + 1) s .(Server.PendingOperations))) with (drop (index + 1) s .(Server.PendingOperations)) by reflexivity.
                rewrite <- drop_drop. rewrite H_nexts. split.
                { reflexivity. }
                assert (index <= uint.nat ns2 .(Slice.sz))%nat as claim3.
                { rewrite <- claim2. rewrite -> claim1. unfold coq_deleteAtIndexOperation. rewrite length_app length_take length_drop. word. }
                assert (length (take index s .(Server.PendingOperations) ++ drop 1 (cur :: nexts)) = uint.nat ns2 .(Slice.sz)) as claim4.
                { rewrite length_app length_take. simpl. replace (drop 0 nexts) with nexts by reflexivity. rewrite <- claim2.
                  rewrite claim1. unfold coq_deleteAtIndexOperation. rewrite length_app length_take length_drop.
                  replace (uint.nat (W64 index)) with index by word. replace (index `min` length s .(Server.PendingOperations))%nat with index by word. word.
                }
                assert (is_sorted (take index (take index s .(Server.PendingOperations) ++ drop 1 (cur :: nexts)) ++ nexts)) as claim5.
                { replace is_sorted with (SessionPrelude.isSorted (hsOrd := hsOrd_Operation n)) by reflexivity. eapply SessionPrelude.isSorted_middle_1 with (y := cur).
                  replace SessionPrelude.isSorted with is_sorted by reflexivity. simpl. replace (drop 0 nexts) with nexts by reflexivity. rewrite take_app.
                  rewrite take_take. replace (index `min` index)%nat with index by word. rewrite length_take. replace (index - index `min` length s .(Server.PendingOperations))%nat with 0%nat by word.
                  replace (take 0 nexts) with ( @nil Operation.t) by reflexivity. rewrite app_nil_r. done.
                }
                replace (take (index - length (take index s .(Server.PendingOperations))) (drop 1 (cur :: nexts))) with ( @nil Operation.t); cycle 1.
                { symmetry. eapply nil_length_inv. rewrite length_take. simpl. rewrite length_drop. rewrite length_take. word. }
                enough (length (coq_maxTS s .(Server.VectorClock) cur .(Operation.VersionVector)) = length s0 .(Server.VectorClock)) by done.
                rewrite <- H1_invariant. revert H1_op2. subst n. rewrite <- H1_invariant. clear. generalize (s .(Server.VectorClock)) as xs. generalize (cur .(Operation.VersionVector)) as ys.
                induction ys as [ | y ys IH], xs as [ | x xs]; simpl; intros; try congruence.
                f_equal. eapply IH. word.
            }
          + wp_load. wp_store. iModIntro. iApply "HΦ".
            iExists (prevs ++ [cur])%list. iExists nexts. iExists (index + 1)%nat. iExists _. iExists UnsatisfiedRequests. iExists VectorClock. iExists OperationsPerformed. iExists PendingOperations. iExists GossipAcknowledgements.
            iSplitL "".
            { iPureIntro. rewrite <- app_assoc. simpl. exact H_split_focus. }
            iSplitL "".
            { iPureIntro. rewrite fold_left_app. simpl. unfold loop_step at 1. rewrite <- H_loop. simpl. rewrite Heqb1. reflexivity. }
            simpl. replace ((w64_word_instance .(word.add) (W64 index) (W64 1))) with ((W64 (index + 1)%nat)) by word. iFrame. iPureIntro.
            subst n. rewrite H_length. simpl. split. { word. }
            split. { rewrite <- drop_drop. rewrite H_nexts. reflexivity. }
            repeat split; trivial.
            { replace (take (index + 1) s .(Server.PendingOperations) ++ nexts) with ((take index s .(Server.PendingOperations) ++ [cur]) ++ nexts).
              - rewrite <- app_assoc. simpl. trivial.
              - rewrite <- take_drop with (l := s .(Server.PendingOperations)) (i := index).
                rewrite take_app. rewrite take_take. replace (index `min` index)%nat with index by word.
                replace (take (index - length (take index s .(Server.PendingOperations))) (drop index s .(Server.PendingOperations))) with ( @nil Operation.t); cycle 1.
                { symmetry. eapply nil_length_inv. rewrite length_take. rewrite length_take. rewrite length_drop. word. }
                rewrite H_nexts. rewrite app_nil_r. f_equal.
                replace (take index s .(Server.PendingOperations) ++ cur :: nexts) with ((take index s .(Server.PendingOperations) ++ [cur]) ++ nexts); cycle 1.
                { rewrite <- app_assoc. reflexivity. }
                rewrite take_app. replace (take (index + 1 - length (take index s .(Server.PendingOperations) ++ [cur])) nexts) with ( @nil Operation.t); cycle 1.
                { symmetry. eapply nil_length_inv. rewrite length_take. rewrite length_app. simpl.  rewrite length_take. word. }
                rewrite app_nil_r. rewrite take_app. rewrite take_take. replace ((index + 1) `min` index)%nat with index by word.
                rewrite length_take. replace (index + 1 - index `min` length s .(Server.PendingOperations))%nat with 1%nat by word. reflexivity.
            }
            { word. }
            { simpl in H_length. word. }
            { congruence. }
        - iModIntro. iApply "HΦ". iExists prevs. iExists nexts. iExists index. iExists _. iExists UnsatisfiedRequests. iExists VectorClock. iExists OperationsPerformed. iExists PendingOperations. iExists GossipAcknowledgements.
          assert (index = uint.nat PendingOperations .(Slice.sz)) as claim1 by word.
          iAssert ⌜nexts = []⌝%I as "%NIL".
          { iPureIntro. rewrite <- H_nexts. eapply nil_length_inv.
            rewrite length_drop. word.
          }
          iFrame. iPureIntro. done.
      }
      { iExists []. iExists focus. iExists 0%nat. iExists (snd loop_init). simpl. iExists _. iExists _. iExists _. iExists _. iExists _.
        iSplitL "". { done. }
        iSplitL "". { iPureIntro. simpl. done. }
        iSplitL "H_i". { done. }
        iSplitL "H_server". { iExact "H_server". }
        iDestruct "H31" as "(%a1 & Ha1 & H31)".
        iPoseProof (big_sepL2_length with "[$H31]") as "%claim1".
        iPoseProof (own_slice_sz with "[$Ha1]") as "%claim2".
        iFrame. iPureIntro. 
        repeat (split; trivial).
        - word.
        - word.
        - congruence.
      }
      { iIntros "(%prevs & %nexts & %index & %s & %UnsatisfiedRequests' & %VectorClock' & %OperationsPerformed' & %PendingOperations' & %GossipAcknowledgements' & %H_split_focus & %H_loop & H_i & H_server & H3 & H4 & H6 & H7 & H8 & H20 & H9 & H16 & H27 & %H_length & %H_nexts & %H1_invariant & [%H2_invariant %H2_invariant'] & %H_index & %H3_invariant & %H4_invariant & [%H5_invariant %H6_invariant] & %H_continue)".
        wp_pures. wp_load. iModIntro.
        set (r := (s .(Server.Id), s .(Server.NumberOfServers), UnsatisfiedRequests', VectorClock', OperationsPerformed', MyOperations, PendingOperations', GossipAcknowledgements')).
        replace (Φ (#s .(Server.Id), (#s .(Server.NumberOfServers), (UnsatisfiedRequests', (VectorClock', (OperationsPerformed', (MyOperations, (PendingOperations', (GossipAcknowledgements', #()))))))))%V) with (Φ (#r.1.1.1.1.1.1.1, (#r.1.1.1.1.1.1.2, (r.1.1.1.1.1.2, (r.1.1.1.1.2, (r.1.1.1.2, (r.1.1.2, (r.1.2, (r.2, #()))))))))%V) by f_equal.
        iApply "HΦ". subst r. simpl. unfold coq_receiveGossip. destruct (length msg .(Message.S2S_Gossip_Operations) =? 0) as [ | ] eqn: H_OBS.
        - rewrite Z.eqb_eq in H_OBS. iDestruct "H16" as "(%ops1 & Hops1 & H16)".
          iPoseProof (big_sepL2_length with "[$H16]") as "%claim1".
          iPoseProof (own_slice_sz with "[$Hops1]") as "%claim2".
          word.
        - simpl. fold focus. fold loop_init. fold loop_step. specialize (H_continue eq_refl). subst nexts.
          rewrite H_continue in H_split_focus. rewrite app_nil_r in H_split_focus. subst prevs.
          rewrite <- H_loop. simpl. iFrame. iPureIntro. repeat (split; trivial).
          + word.
          + word.
          + rewrite take_drop in H2_invariant. done.
          + done.
          + done.
      } *)
  Admitted.

  Lemma wp_acknowledgeGossip {OWN_UnsatisfiedRequests: bool} sv s msgv msg (n: nat) len_c2s len_s2c len_vc len_op len_mo len_po len_ga :
    {{{
        is_server' sv s n len_vc len_op len_mo len_po len_ga OWN_UnsatisfiedRequests ∗ 
        is_message msgv msg n len_c2s len_s2c
    }}}
      CoqSessionServer.acknowledgeGossip (server_val sv) (message_val msgv)
    {{{
        RET (server_val sv);
        is_server' sv (coq_acknowledgeGossip s msg) n len_vc len_op len_mo len_po len_ga OWN_UnsatisfiedRequests ∗
        is_message msgv msg n len_c2s len_s2c
    }}}.
  Proof.
    TypeVector.des sv. TypeVector.des msgv.
    iIntros "%Φ (H_server & H_message) HΦ". rewrite /acknowledgeGossip.
    iDestruct "H_server" as "(%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10)".
    iDestruct "H_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & %H19 & H20 & %H21 & %H22 & %H23 & %H24 & %H25 & %H26 & H27 & %H28 & %H29 & %H30)".
    simplNotation. subst. rewrite redefine_message_val redefine_server_val. simpl in *. wp_pures.
    wp_apply (wp_slice_len). wp_if_destruct.
    - iModIntro. iApply "HΦ". unfold coq_acknowledgeGossip.
      destruct (uint.nat msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) >=? length s.(Server.GossipAcknowledgements))%nat as [ | ] eqn: H_OBS; simpl.
      + iFrame. iPureIntro. done.
      + rewrite Z.geb_leb in H_OBS. rewrite Z.leb_gt in H_OBS.
        iPoseProof (own_slice_small_sz with "[$H9]") as "%YES1".
        word.
    - iPoseProof (own_slice_small_sz with "[$H9]") as "%YES2".
      assert (uint.nat msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId) < length s.(Server.GossipAcknowledgements))%nat as YES1 by word.
      apply list_lookup_lt in YES1. destruct YES1 as [x H_x].
      wp_apply (wp_SliceGet with "[$H9]"); auto. iIntros "H9". wp_apply (wp_maxTwoInts with "[]"); auto.
      iIntros "%r ->". wp_apply (slice.wp_SliceSet with "[H9]").
      { iSplitL "H9".
        - iExact "H9".
        - iPureIntro. split; auto.
          exists (u64_IntoVal.(to_val) x). cbn.
          rewrite list_lookup_fmap. rewrite H_x. done.
      }
      iIntros "H9". wp_pures. iModIntro. iApply "HΦ". iFrame. iSplitR "".
      + unfold is_server'. simplNotation. unfold coq_acknowledgeGossip.
        destruct (uint.nat msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) >=? length s.(Server.GossipAcknowledgements))%nat as [ | ] eqn: H_OBS; simpl.
        * rewrite Z.geb_ge in H_OBS. word.
        * rewrite H_x. simpl. iFrame.
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "H9".
          { unfold own_slice_small. unfold list.untype. cbn. rewrite list_fmap_insert. done. }
          { rewrite length_insert. done. }
      + iPureIntro. done.
  Qed.

  Lemma wp_getGossipOperations {OWN_UnsatisfiedRequests: bool} sv s(serverId: u64) (n: nat) len_vc len_op len_mo len_po len_ga :
    {{{
        is_server' sv s n len_vc len_op len_mo len_po len_ga OWN_UnsatisfiedRequests
    }}}
      CoqSessionServer.getGossipOperations (server_val sv) (#serverId)
    {{{
        ns, RET (slice_val ns);
        operation_slice ns (coq_getGossipOperations s serverId) len_mo ∗
        is_server' sv s n len_vc len_op len_mo len_po len_ga OWN_UnsatisfiedRequests
    }}}.
  Proof.
    TypeVector.des sv. iIntros "%Φ (%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10) HΦ".
    simplNotation. subst. rewrite /getGossipOperations. wp_pures.
    wp_apply wp_NewSlice; auto. iIntros "%s1 [H1_s1 H2_s1]".
    iPoseProof (own_slice_small_sz with "[$H1_s1]") as "%H_s1_len".
    iPoseProof (own_slice_small_sz with "[$H9]") as "%YES1".
    iPoseProof (own_slice_small_sz with "[$H4]") as "%YES2".
    wp_apply wp_ref_to; auto. iIntros "%ret H_ret".
    wp_pures. wp_bind (if: #serverId ≥ slice.len t then #true else _)%E.
    wp_apply wp_slice_len; auto. wp_if_destruct.
    - wp_pures. wp_load. iModIntro. iApply "HΦ". iFrame.
      replace (replicate (uint.nat (W64 0)) operation_into_val .(IntoVal_def (Slice.t * w64))) with ( @nil (Slice.t * w64)) in *; simpl in *; trivial. iSplitL "".
      + unfold coq_getGossipOperations. replace (s.(Server.GossipAcknowledgements) !! uint.nat serverId) with ( @None u64).
        * iApply big_sepL2_nil. done.
        * symmetry. eapply lookup_ge_None. word.
      + iPureIntro. tauto.
    - wp_pures. wp_apply wp_slice_len; auto.
      assert (is_Some (s .(Server.GossipAcknowledgements) !! uint.nat serverId)) as [v H_v].
      { eapply lookup_lt_is_Some_2. word. }
      wp_apply (wp_SliceGet with "[$H9]"); auto.
      iIntros "H1". simpl. wp_pures. wp_if_destruct.
      + wp_load. iModIntro. iApply "HΦ". iDestruct "H7" as "[%ops [H7 H9]]". unfold tuple_of in *. simpl in *.
        iPoseProof (own_slice_sz with "[$H7]") as "%YES3".
        iPoseProof (big_sepL2_length with "[$H9]") as "%YES4".
        iFrame. simpl in *. replace (replicate (uint.nat (W64 0)) (Slice.nil, W64 0)) with ( @nil (Slice.t * w64)) in *; simpl in *; trivial. iSplitL "".
        * unfold coq_getGossipOperations. rewrite H_v. rewrite skipn_all2.
          { simpl. done. }
          { word. }
        * iPureIntro. tauto.
      + rewrite redefine_server_val. simpl. wp_pures.
        wp_apply (wp_SliceGet with "[$H1]"); auto. iIntros "H9". simpl in *.
        wp_pures. wp_apply wp_SliceSkip; auto. { word. } wp_load. iDestruct "H7" as "(%ops & [H7 H10] & H11)".
        iPoseProof (own_slice_small_sz with "[$H7]") as "%YES3".
        iPoseProof (big_sepL2_length with "[$H11]") as "%YES4".
        iPoseProof (slice_small_split with "[$H7]") as "[H7 H7']".
        { instantiate (1 := v). word. }
        wp_apply (wp_SliceAppendSlice with "[$H1_s1 $H2_s1 H7']"); auto.
        iIntros "%s2 [H1_s2 H2_s2]". replace (replicate (uint.nat (W64 0)) (Slice.nil, W64 0)) with ( @nil (Slice.t * w64)) in * by reflexivity. simpl in *.
        iApply "HΦ". iPoseProof (pers_big_sepL2_is_operation with "[$H11]") as "#H10_pers". iFrame.
        iSplitL "".
        { unfold coq_getGossipOperations. rewrite H_v. rewrite <- take_drop with (l := ops) (i := uint.nat v) at 1. rewrite <- take_drop with (l := s.(Server.MyOperations)) (i := uint.nat v) at 1.
          iPoseProof (big_sepL2_app_equiv with "[$H10_pers]") as "[YES1 YES2]".
          - do 2 rewrite length_take. word.
          - iExact "YES2".
        }
        iSplitL "". { iPureIntro. tauto. }
        iSplitL "". { iPureIntro. tauto. }
        iSplitL "". { iPureIntro. tauto. }
        iSplitR "".
        { iApply own_slice_small_take_drop.
          - instantiate (1 := v). simplNotation. word.
          - iFrame.
        }
        iPureIntro. tauto. 
  Qed.

End heap.

#[global] Opaque CoqSessionServer.deleteAtIndexOperation.
#[global] Opaque CoqSessionServer.deleteAtIndexMessage.
#[global] Opaque CoqSessionServer.getDataFromOperationLog.
#[global] Opaque CoqSessionServer.receiveGossip.
#[global] Opaque CoqSessionServer.acknowledgeGossip.
#[global] Opaque CoqSessionServer.getGossipOperations.
