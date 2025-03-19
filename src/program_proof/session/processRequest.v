From Perennial.program_proof.session Require Export session_prelude coq_session.
From Perennial.program_proof.session Require Export versionVector processClientRequest gossip.

Section heap.

  Context `{hG: !heapGS Σ}.

  Lemma wp_processClientRequest sv s msgv msg (n: nat) (m: nat) len_po len_ga len_c2s len_s2c :
    {{{
        is_server sv s n m m m len_po len_ga ∗
        is_message msgv msg n len_c2s len_s2c ∗
        ⌜m = len_c2s /\ INVARIANT.SERVER s⌝
    }}}
      processClientRequest (server_val sv) (message_val msgv)
    {{{
        (b: bool) ns nm, RET (#b, server_val ns, message_val nm);
        ⌜b = (coq_processClientRequest s msg).1.1⌝ ∗
        is_server ns (coq_processClientRequest s msg).1.2 n m m m len_po len_ga ∗
        is_message nm (coq_processClientRequest s msg).2 n 0%nat (if b then len_c2s else 0%nat) ∗
        is_message msgv msg n len_c2s len_s2c ∗
        ⌜INVARIANT.SERVER (coq_processClientRequest s msg).1.2⌝
    }}}.
  Proof.
    rewrite redefine_server_val redefine_message_val. TypeVector.des sv. TypeVector.des msgv. iIntros "%Φ (H_server & H_message & %H1_precondition & %H2_precondition) HΦ". destruct H2_precondition as [? ? ? ?].
    iDestruct "H_server" as "(%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10)".
    iDestruct "H_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & %H19 & H20 & %H21 & %H22 & %H23 & %H24 & %H25 & %H26 & H27 & %H28 & %H29 & %H30)".
    simplNotation. subst. rewrite /processClientRequest.
    wp_pures. wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. }
    iIntros "%reply H_reply". wp_pures. wp_apply (wp_compareVersionVector with "[$H4 $H16]"); auto.
    iIntros "%r (-> & H4 & [H16 %TMP])". clear TMP. wp_if_destruct.
    - wp_load. wp_pures. iModIntro.
      pose (b := false).
      set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)).
      set (nm := (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)).
      replace (Φ (#false, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #())))))))), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #())))))))))))))))))))%V) with (Φ (#b, (#ns.1.1.1.1.1.1.1, (#ns.1.1.1.1.1.1.2, (ns.1.1.1.1.1.2, (ns.1.1.1.1.2, (ns.1.1.1.2, (ns.1.1.2, (ns.1.2, (ns.2, #())))))))), (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.2, (#nm.1.1.1.1.2, (#nm.1.1.1.2, (nm.1.1.2, (#nm.1.2, (#nm.2, #())))))))))))))))))))%V) by f_equal.
      unfold tuple_of. simpl TypeVector.tuple_of. iApply "HΦ". subst b ns nm.
      unfold coq_processClientRequest. rewrite Heqb. simpl. iFrame.
      unfold is_message; simplNotation; simpl. iClear "H_reply". repeat (iSplit; try done).
      iSplitL "". { iApply own_slice_small_nil. done. } repeat (iSplit; try done).
      iSplitL "".
      { iExists []. iSplit.
        - iApply own_slice_nil; done.
        - simpl. done.
      }
      repeat (iSplit; try done).
      iApply own_slice_small_nil. done.
    - wp_pures. wp_if_destruct.
      + wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
        wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
        wp_apply (wp_getDataFromOperationLog with "[$H6]"). iIntros "%r (-> & H6)".
        wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
        wp_apply (wp_NewSlice). iIntros "%s1 H_s1". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil u64 ) by reflexivity.
        wp_apply (wp_SliceAppendSlice with "[$H_s1 $H4]"); auto. clear s1. iIntros "%s1 [H_s1 H4]". simpl.
        wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
        wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
        wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
        wp_load. wp_pures. iModIntro. simpl.
        pose (b := true).
        set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)).
        set (nm := (W64 4, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, coq_getDataFromOperationLog s .(Server.OperationsPerformed), s1, s .(Server.Id), msg .(Message.C2S_Client_Id))).
        replace (Φ (#true, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #())))))))), (#(W64 4), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (#(W64 0), (#(coq_getDataFromOperationLog s .(Server.OperationsPerformed)), (s1, (#s .(Server.Id), (#msg .(Message.C2S_Client_Id), #())))))))))))))))))))%V) with (Φ (#b, server_val ns, message_val nm)%V) by f_equal.
        unfold server_val, message_val. iApply "HΦ". subst b ns nm.
        unfold coq_processClientRequest; rewrite Heqb; simpl.
        assert ((uint.nat msg .(Message.C2S_Client_OperationType) =? 0) = true) as H_OBS1.
        { rewrite Z.eqb_eq. word. }
        rewrite H_OBS1; simpl. unfold is_message; simplNotation; simpl. rewrite Z.eqb_eq in H_OBS1.
        iSplitL "". { done. }
        iSplitL "H3 H7 H8 H9 H6 H4".
        { iFrame. done. }
        { iSplitL "H_s1".
          - repeat (iSplit; try done). iSplitL "".
            { iApply own_slice_small_nil. reflexivity. }
            repeat (iSplit; try done). iSplitL "".
            { iExists []; simpl; iSplit.
              - iApply own_slice_nil; reflexivity.
              - iPureIntro. tauto.
            }
            repeat (iSplit; try done). iApply (own_slice_to_small with "[$H_s1]").
          - iFrame. done.
        }
      + wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%s1 H_s1". wp_pures.
        iAssert ⌜is_Some (s .(Server.VectorClock) !! uint.nat s .(Server.Id))⌝%I as "[%x %H_x]".
        { iPoseProof (own_slice_small_sz with "[$H4]") as "%LEN".
          iPureIntro. eapply lookup_lt_is_Some_2. word.
        }
        wp_load. wp_pures. wp_apply (wp_SliceGet with "[$H4]"); auto. iIntros "H4".
        wp_load. wp_pures. wp_apply (wp_SliceSet with "[$H4]"); auto. iIntros "H4".
        wp_pures. wp_apply (wp_NewSlice). iIntros "%s2 H_s2". wp_apply (wp_SliceAppendSlice with "[$H_s2 $H4]"); auto.
        clear s2. iIntros "%s2 [H_s2 H4]". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil w64 ) by reflexivity. simpl.
        iDestruct "H_s2" as "[H1_s2 H2_s2]". iMod (own_slice_small_persist with "[$H1_s2]") as "H1_s2".
        wp_pures. wp_load. wp_pures. replace (s2, (#msg .(Message.C2S_Client_Data), #()))%V with (to_val (s2, msg .(Message.C2S_Client_Data))) by reflexivity.
        iDestruct "H6" as "(%t2_ops & H6 & H_t2_ops)". wp_apply (another_wp_sortedInsert with "[$H6 $H_t2_ops H1_s2]"). { instantiate (1 := {| Operation.VersionVector := (<[uint.nat s .(Server.Id):=w64_word_instance .(word.add) x (W64 1)]> s .(Server.VectorClock)); Operation.Data := msg .(Message.C2S_Client_Data); |}). apply list_lookup_total_correct in H_x. subst x. unfold lookup_total. iFrame. rewrite length_insert. done. } iIntros "%s3 (H_s3 & %H1_sorted)".
        wp_pures. wp_apply (wp_storeField_struct with "[H_s1]"). { repeat econstructor; eauto. } { iExact "H_s1". } iIntros "H_s1".
        wp_pures. wp_load. wp_pures. replace (SliceAppendSlice uint64T slice.nil t3) with (SliceAppendSlice uint64T Slice.nil t3) by reflexivity.
        wp_apply (wp_SliceAppendSlice with "[H4]"). { repeat econstructor; eauto. } { instantiate (5 := @nil u64). iSplitR "H4"; try done. iApply own_slice_nil; done. } iIntros "%s4 [H_s4 H4]".
        iDestruct "H7" as "(%t1_ops & H7 & H_t1_ops)". iDestruct "H_s4" as "[H1_s4 H2_s4]". iMod (own_slice_small_persist with "[$H1_s4]") as "H1_s4".
        wp_load. wp_pures. replace (s4, (#msg .(Message.C2S_Client_Data), #()))%V with (to_val (s4, msg .(Message.C2S_Client_Data))) by reflexivity. simpl.
        wp_apply (another_wp_sortedInsert with "[H7 H_t1_ops H1_s4]").
        { iSplitL "H7 H_t1_ops".
          - iExists t1_ops. iFrame.
          - instantiate (1 := {| Operation.VersionVector := (<[uint.nat s .(Server.Id):=w64_word_instance .(word.add) x (W64 1)]> s .(Server.VectorClock)); Operation.Data := msg .(Message.C2S_Client_Data); |}). simpl. iSplitL "H1_s4".
            + iFrame. rewrite length_insert. done.
            + done.
        }
        iIntros "%s5 (H_s5 & %H2_sorted)". wp_apply (wp_storeField_struct with "[H_s1]"). { repeat econstructor; eauto. } { iExact "H_s1". } iIntros "H_s1".
        wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
        wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
        wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
        wp_pures. wp_apply (wp_NewSlice). iIntros "%s6 H_s6".
        wp_pures. wp_apply (wp_SliceAppendSlice with "[$H_s6 $H4]"); eauto. clear s6. iIntros "%s6 [H_s6 H4]".
        wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
        wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
        wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
        wp_pures. wp_load. wp_pures. wp_load. wp_pures.
        iModIntro.
        pose (b := true).
        set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, s3, s5, t0, t)).
        set (nm := (W64 4, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 1, W64 0, s6, s .(Server.Id), msg .(Message.C2S_Client_Id))).
        replace (Φ (#true, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (s3, (s5, (t0, (t, #())))))))), (#(W64 4), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (#(W64 1), (#(W64 0), (s6, (#s .(Server.Id), (#msg .(Message.C2S_Client_Id), #())))))))))))))))))))%V) with (Φ (#b, server_val ns, message_val nm)%V) by f_equal.
        unfold server_val, message_val. iApply "HΦ". subst b ns nm. simpl.
        unfold coq_processClientRequest; rewrite Heqb; simpl.
        assert ((uint.nat msg .(Message.C2S_Client_OperationType) =? 0) = false) as H_OBS1.
        { rewrite Z.eqb_neq. word. }
        rewrite H_OBS1; simpl. unfold is_message; simplNotation; simpl. rewrite Z.eqb_neq in H_OBS1.
        iSplitL "". { done. }
        iSplitL "H3 H4 H_s3 H_s5 H8 H9".
        { apply list_lookup_total_correct in H_x. subst x. unfold lookup_total.
          replace (w64_word_instance .(word.add) (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) (W64 1)) with (W64 (uint.nat (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) + 1)) in * by word.
          iFrame; simpl; simplNotation. repeat rewrite length_insert. repeat (iSplit; try done).
        }
        repeat rewrite length_insert.
        iSplitL "H_s6".
        { apply list_lookup_total_correct in H_x. subst x. unfold lookup_total.
          replace (replicate (uint.nat (W64 0)) (W64 0)) with ( @nil u64 ) by reflexivity. simpl.
          replace (w64_word_instance .(word.add) (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) (W64 1)) with (W64 (uint.nat (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) + 1)) by word.
          repeat (iSplit; try done). iSplitL "". { iApply own_slice_small_nil; eauto. }
          repeat (iSplit; try done). iSplitL "".
          { iExists []. iSplit.
            - iApply own_slice_nil; eauto.
            - simpl. done.
          }
          repeat (iSplit; try done). iApply (own_slice_to_small with "[$H_s6]").
        }
        iSplitL "H20 H27 H16".
        { iFrame. done. }
        apply list_lookup_total_correct in H_x. subst x. unfold lookup_total in *.
        replace (w64_word_instance .(word.add) (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) (W64 1)) with (W64 (uint.nat (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) + 1)) in * by word.
        iPureIntro. split; simpl; trivial.
        rewrite length_insert. word.
  Qed.

  Lemma wp_processRequest sv s msgv msg (n: nat) (m: nat) len_po len_ga len_c2s len_s2c :
    {{{
        is_server sv s n m m m len_po len_ga ∗
        is_message msgv msg n len_c2s len_s2c ∗
        ⌜m = len_c2s /\ INVARIANT.SERVER s⌝
    }}}
      processRequest (server_val sv) (message_val msgv)
    {{{
        ns nms, RET (server_val ns, slice_val nms);
        is_server ns (coq_processRequest s msg).1 n m m m len_po len_ga ∗
        message_slice nms (coq_processRequest s msg).2 n ∗
        ⌜INVARIANT.SERVER (coq_processRequest s msg).1⌝
    }}}.
  Proof. (**
    assert (rewrite_nil : forall A : Type, forall x : A, forall n : nat, n = 0%nat -> replicate n x = []) by now intros; subst; reflexivity.
    rewrite redefine_server_val redefine_message_val. TypeVector.des sv. TypeVector.des msgv. iIntros "%Φ (H_server & H_message & %H_precondition) HΦ".
    iDestruct "H_server" as "(%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10)".
    iDestruct "H_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & %H19 & H20 & %H21 & %H22 & %H23 & %H24 & %H25 & %H26 & H27 & %H28 & %H29 & %H30)".
    unfold INVARIANT.SERVER in *. destruct H_precondition as (H1_precondition & H2_precondition & H3_precondition); simplNotation; subst; rewrite /processRequest.
    wp_pures. wp_apply wp_NewSlice. simpl. rewrite rewrite_nil; cycle 1. { word. } iIntros "%s1 H_s1".
    wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%outGoingRequests H_outGoingRequests".
    wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%server H_server".
    wp_pures. wp_if_destruct.
    { wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%succeeded H_succeeded".
      wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%reply H_reply".
      wp_pures. wp_load. replace (processClientRequest (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #()))))))))%V (#msg .(Message.MessageType), (#msg .(Message.C2S_Client_Id), (#msg .(Message.C2S_Server_Id), (#msg .(Message.C2S_Client_OperationType), (#msg .(Message.C2S_Client_Data), (t7, (#msg .(Message.S2S_Gossip_Sending_ServerId), (#msg .(Message.S2S_Gossip_Receiving_ServerId), (t6, (#msg .(Message.S2S_Gossip_Index), (#msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Index), (#msg .(Message.S2C_Client_OperationType), (#msg .(Message.S2C_Client_Data), (t5, (#msg .(Message.S2C_Server_Id), (#msg .(Message.S2C_Client_Number), #()))))))))))))))))))%V) with (processClientRequest (server_val (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)) (message_val (msg .(Message.MessageType), msg .(Message.C2S_Client_Id), msg .(Message.C2S_Server_Id), msg .(Message.C2S_Client_OperationType), msg .(Message.C2S_Client_Data), t7, msg .(Message.S2S_Gossip_Sending_ServerId), msg .(Message.S2S_Gossip_Receiving_ServerId), t6, msg .(Message.S2S_Gossip_Index), msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Index), msg .(Message.S2C_Client_OperationType), msg .(Message.S2C_Client_Data), t5, msg .(Message.S2C_Server_Id), msg .(Message.S2C_Client_Number)))) by f_equal.
      wp_apply (wp_processClientRequest with "[H3 H4 H6 H7 H8 H9 H16 H20 H27]"). { iFrame. simplNotation; subst. done. } iIntros "%b %ns %nm (%len_c2s' & %len_s2c' & -> & H_server' & H_message' & H_message & %H1_postcondition)".
      wp_store. wp_store. wp_pures; lazymatch goal with [ |- envs_entails _ (wp ?s ?E (App ?k ?e)%E ?Q) ] => eapply (tac_wp_store_ty _ _ _ _ _ _ [AppRCtx k]%list); [repeat econstructor; eauto | tc_solve | let l := reply in iAssumptionCore | reflexivity | simpl] end.
      wp_pures. wp_load. wp_if_destruct.
      - wp_load. wp_load. replace message_val with (message_into_val .(to_val)) by reflexivity. wp_apply (wp_SliceAppend with "[$H_s1]"). iIntros "%s2 H_s2".
        wp_store. wp_load. wp_load. wp_pures. simpl. iModIntro. iApply "HΦ".
        unfold coq_processRequest; rewrite Heqb; replace (uint.nat (W64 0)) with 0%nat by reflexivity. destruct (coq_processClientRequest s msg) as [[succeeded_v s_v] reply_v] eqn: H_OBS; simpl in *.
        destruct H1_postcondition as [-> ->]; subst succeeded_v; simpl in *. iFrame. simpl.
      - wp_load. wp_pures. iDestruct "H_server'" as "(%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10)". iDestruct "H_message'" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & %H19 & H20 & %H21 & %H22 & %H23 & %H24 & %H25 & %H26 & H27 & %H28 & %H29 & %H30)". simplNotation; subst.
        replace (#msg .(Message.MessageType), (#msg .(Message.C2S_Client_Id), (#msg .(Message.C2S_Server_Id), (#msg .(Message.C2S_Client_OperationType), (#msg .(Message.C2S_Client_Data), (t7, (#msg .(Message.S2S_Gossip_Sending_ServerId), (#msg .(Message.S2S_Gossip_Receiving_ServerId), (t6, (#msg .(Message.S2S_Gossip_Index), (#msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Index), (#msg .(Message.S2C_Client_OperationType), (#msg .(Message.S2C_Client_Data), (t5, (#msg .(Message.S2C_Server_Id), (#msg .(Message.S2C_Client_Number), #()))))))))))))))))))%V with (message_into_val .(to_val) (msg .(Message.MessageType), msg .(Message.C2S_Client_Id), msg .(Message.C2S_Server_Id), msg .(Message.C2S_Client_OperationType), msg .(Message.C2S_Client_Data), t7, msg .(Message.S2S_Gossip_Sending_ServerId), msg .(Message.S2S_Gossip_Receiving_ServerId), t6, msg .(Message.S2S_Gossip_Index), msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Index), msg .(Message.S2C_Client_OperationType), msg .(Message.S2C_Client_Data), t5, msg .(Message.S2C_Server_Id), msg .(Message.S2C_Client_Number))) by reflexivity.
        iDestruct "H3" as "(%ops1 & H3 & H_ops1)". wp_apply (wp_SliceAppend with "[$H3]"). iIntros "%s2 H_s2". wp_apply (wp_storeField_struct with "[H_server]"); auto. iIntros "H_server".
        wp_pures. wp_load. wp_load. wp_pures. iModIntro. red in ns, nm. simpl in ns, nm. replace (Φ (#ns.1.1.1.1.1.1.1, (#ns.1.1.1.1.1.1.2, (s2, (ns.1.1.1.1.2, (ns.1.1.1.2, (ns.1.1.2, (ns.1.2, (ns.2, #()))))))), s1)%V) with (Φ (server_val (ns.1.1.1.1.1.1.1, ns.1.1.1.1.1.1.2, s2, ns.1.1.1.1.2, ns.1.1.1.2, ns.1.1.2, ns.1.2, ns.2)%core, s1)%V) by reflexivity. iApply "HΦ".
        unfold coq_processRequest; rewrite Heqb; replace (uint.nat (W64 0)) with 0%nat by reflexivity. do 7 destruct ns as [ns ?]; simpl in *. do 17 destruct nm as [nm ?]; simpl in *. subst.
        destruct (coq_processClientRequest s msg) as [[b s'] msg'] eqn: H_OBS; simpl in *. rewrite Heqb0; simpl. iFrame; simplNotation; simpl. done.
    }
    wp_if_destruct.
    { wp_load. replace (receiveGossip (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #()))))))))%V (#msg .(Message.MessageType), (#msg .(Message.C2S_Client_Id), (#msg .(Message.C2S_Server_Id), (#msg .(Message.C2S_Client_OperationType), (#msg .(Message.C2S_Client_Data), (t7, (#msg .(Message.S2S_Gossip_Sending_ServerId), (#msg .(Message.S2S_Gossip_Receiving_ServerId), (t6, (#msg .(Message.S2S_Gossip_Index), (#msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Index), (#msg .(Message.S2C_Client_OperationType), (#msg .(Message.S2C_Client_Data), (t5, (#msg .(Message.S2C_Server_Id), (#msg .(Message.S2C_Client_Number), #()))))))))))))))))))%V) with (receiveGossip (server_val (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)) (message_val( msg .(Message.MessageType), msg .(Message.C2S_Client_Id), msg .(Message.C2S_Server_Id), msg .(Message.C2S_Client_OperationType), msg .(Message.C2S_Client_Data), t7, msg .(Message.S2S_Gossip_Sending_ServerId), msg .(Message.S2S_Gossip_Receiving_ServerId), t6, msg .(Message.S2S_Gossip_Index), msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Index), msg .(Message.S2C_Client_OperationType), msg .(Message.S2C_Client_Data), t5, msg .(Message.S2C_Server_Id), msg .(Message.S2C_Client_Number)))) by f_equal.
      wp_apply (wp_receiveGossip with "[H3 H4 H6 H7 H8 H9 H16 H20 H27]"). { iFrame. simplNotation; subst. done. }
    }
  Qed. *) Admitted.

End heap.
