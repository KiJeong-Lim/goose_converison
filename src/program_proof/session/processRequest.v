From Perennial.program_proof.session Require Export session_prelude coq_session.
From Perennial.program_proof.session Require Export versionVector sort gossip.

Section heap.
  Context `{hG: !heapGS Σ}.

  #[local] Hint Constructors Forall : core.

  Lemma wp_processClientRequest {OWN_UnsatisfiedRequests: bool} UnsatisfiedRequests GossipAcknowledgements sv s msgv msg (n: nat) (m: nat) len_po len_ga len_s2c :
    {{{
        is_server' sv s n m m m len_po len_ga OWN_UnsatisfiedRequests ∗
        is_message msgv msg n m len_s2c ∗
        ⌜SERVER_INVARIANT (fun _s => _s.(Server.UnsatisfiedRequests) = UnsatisfiedRequests /\ _s.(Server.GossipAcknowledgements) = GossipAcknowledgements) s⌝
    }}}
      CoqSessionServer.processClientRequest (server_val sv) (message_val msgv)
    {{{
        b ns nm, RET (#b, server_val ns, message_val nm);
        ⌜b = (coq_processClientRequest s msg).1.1⌝ ∗
        is_server' ns (coq_processClientRequest s msg).1.2 n m m m len_po len_ga OWN_UnsatisfiedRequests ∗
        is_message nm (coq_processClientRequest s msg).2 n 0%nat (if b then m else 0%nat) ∗
        is_message msgv msg n m len_s2c ∗
        ⌜SERVER_INVARIANT (fun _s => _s.(Server.UnsatisfiedRequests) = UnsatisfiedRequests /\ _s.(Server.GossipAcknowledgements) = GossipAcknowledgements) (coq_processClientRequest s msg).1.2 /\ sv!(2) = ns!(2)⌝
    }}}.
  Proof.
    set (fun _s => _s.(Server.UnsatisfiedRequests) = UnsatisfiedRequests /\ _s.(Server.GossipAcknowledgements) = GossipAcknowledgements) as EXTRA.
    rewrite redefine_server_val redefine_message_val. TypeVector.des sv. TypeVector.des msgv. iIntros "%Φ (H_server & H_message & %H_precondition) HΦ". destruct H_precondition as [? ? ? ? ?].
    iDestruct "H_server" as "(%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10)".
    iDestruct "H_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & %H19 & H20 & %H21 & %H22 & %H23 & %H24 & %H25 & %H26 & H27 & %H28 & %H29 & %H30)".
    simplNotation. subst. rewrite /processClientRequest. repeat match goal with [ H : ?x = _ /\ _ |- _ ] => let x' := fresh x in rename x into x'; destruct H as [-> H] end.
    wp_pures. wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. }
    iIntros "%reply H_reply". wp_pures. wp_apply (wp_compareVersionVector with "[$H4 $H16]"); try (iPureIntro; word).
    iIntros "%r (H4 & H16 & %H_r)". subst r. wp_if_destruct.
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
        wp_apply (wp_NewSlice). iIntros "%s1 H_s1". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil u64) by reflexivity.
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
        assert ((uint.Z msg .(Message.C2S_Client_OperationType) =? 0)%Z = true) as H_OBS1.
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
        wp_apply wp_ref_to; auto. rewrite <- CONSTANT_minus_1. iIntros "%constant_ref H_constant_ref". wp_load.
        wp_load. wp_pures. wp_apply (wp_SliceGet with "[$H4]"); auto. iIntros "H4". wp_load. simpl. wp_pure. destruct (bool_decide _) as [ | ] eqn: H_OBS1; cycle 1.
        { rewrite bool_decide_eq_false in H_OBS1. wp_pures. wp_load. wp_pures. wp_load. wp_pures. iModIntro.
          pose (b := false).
          set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)).
          set (nm := (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)).
          replace (Φ (#false, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #())))))))), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #())))))))))))))))))))%V) with (Φ (#b, (#ns.1.1.1.1.1.1.1, (#ns.1.1.1.1.1.1.2, (ns.1.1.1.1.1.2, (ns.1.1.1.1.2, (ns.1.1.1.2, (ns.1.1.2, (ns.1.2, (ns.2, #())))))))), (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.2, (#nm.1.1.1.1.2, (#nm.1.1.1.2, (nm.1.1.2, (#nm.1.2, (#nm.2, #())))))))))))))))))))%V) by f_equal.
          unfold tuple_of. simpl TypeVector.tuple_of. iApply "HΦ". subst b ns nm.
          unfold coq_processClientRequest. rewrite Heqb. simpl. replace (uint.Z msg .(Message.C2S_Client_OperationType) =? 0)%Z with false; cycle 1. { symmetry. rewrite Z.eqb_neq. word. } rewrite H_x. replace ((uint.Z x <=? CONSTANT - 1) && (length s .(Server.MyOperations) <=? CONSTANT - 1)) with false; cycle 1.
          { symmetry. rewrite andb_false_iff. left. rewrite Z.leb_nle. rewrite -> CONSTANT_unfold in H_OBS1 |- *. apply SessionPrelude.lookup_In in H_x. destruct H5 as [H5' H5]. rewrite List.Forall_forall in H5. apply H5 in H_x. red in H_x. rewrite CONSTANT_unfold in H_x. word. }
          simpl; iFrame. unfold is_message; simplNotation; simpl. iClear "H_reply". assert (CONSTANT >= 1)%Z as H_ge_1 by (rewrite CONSTANT_unfold; word). revert_until hG. generalize CONSTANT as c. intros. repeat (iSplit; try done).
          iSplitL "". { iApply own_slice_small_nil. done. } repeat (iSplit; try done).
          iSplitL "".
          { iExists []. iSplit.
            - iApply own_slice_nil; done.
            - simpl. done.
          }
          repeat (iSplit; try done).
          iApply own_slice_small_nil. done.
        }
        wp_load. wp_pures. wp_apply wp_slice_len. iAssert ⌜(uint.nat t1.(Slice.sz) = length s.(Server.MyOperations))%nat⌝%I as "%H_t1_slice_sz". { iDestruct "H7" as "(%ops & H7 & H_ops)". iPoseProof (own_slice_sz with "[$H7]") as "%LEN1". iPoseProof (big_sepL2_length with "[$H_ops]") as "%LEN2". word. } wp_load. simpl. wp_pure. destruct (bool_decide (uint.Z t1 .(Slice.sz) ≤ uint.Z (W64 (CONSTANT - 1)))) as [ | ] eqn: H_OBS2; cycle 1.
        { rewrite bool_decide_eq_false in H_OBS2. wp_pures. wp_load. wp_pures. wp_load. wp_pures. iModIntro.
          pose (b := false).
          set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)).
          set (nm := (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)).
          replace (Φ (#false, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #())))))))), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #())))))))))))))))))))%V) with (Φ (#b, (#ns.1.1.1.1.1.1.1, (#ns.1.1.1.1.1.1.2, (ns.1.1.1.1.1.2, (ns.1.1.1.1.2, (ns.1.1.1.2, (ns.1.1.2, (ns.1.2, (ns.2, #())))))))), (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.2, (#nm.1.1.1.1.2, (#nm.1.1.1.2, (nm.1.1.2, (#nm.1.2, (#nm.2, #())))))))))))))))))))%V) by f_equal.
          unfold tuple_of. simpl TypeVector.tuple_of. iApply "HΦ". subst b ns nm.
          unfold coq_processClientRequest. rewrite Heqb. simpl. replace (uint.Z msg .(Message.C2S_Client_OperationType) =? 0)%Z with false; cycle 1. { symmetry. rewrite Z.eqb_neq. word. } rewrite H_x. replace ((uint.Z x <=? CONSTANT - 1) && (length s .(Server.MyOperations) <=? CONSTANT - 1)) with false; cycle 1.
          { symmetry. rewrite andb_false_iff. right. rewrite Z.leb_nle. rewrite -> CONSTANT_unfold in H_OBS2 |- *. apply SessionPrelude.lookup_In in H_x. destruct H5 as [H5' H5]. rewrite List.Forall_forall in H5. apply H5 in H_x. red in H_x. rewrite CONSTANT_unfold in H_x. word. }
          simpl; iFrame. unfold is_message; simplNotation; simpl. iClear "H_reply". assert (CONSTANT >= 1)%Z as H_ge_1 by (rewrite CONSTANT_unfold; word). revert_until hG. generalize CONSTANT as c. intros. repeat (iSplit; try done).
          iSplitL "". { iApply own_slice_small_nil. done. } repeat (iSplit; try done).
          iSplitL "".
          { iExists []. iSplit.
            - iApply own_slice_nil; done.
            - simpl. done.
          }
          repeat (iSplit; try done).
          iApply own_slice_small_nil. done.
        }
        wp_load. wp_pures. wp_apply (wp_SliceGet with "[$H4]"); auto. iIntros "H4".
        wp_load. wp_pures. wp_apply (wp_SliceSet with "[$H4]"); auto. iIntros "H4".
        wp_load. wp_apply (wp_NewSlice). iIntros "%s2 H_s2". wp_apply (wp_SliceAppendSlice with "[$H_s2 $H4]"); auto.
        clear s2. iIntros "%s2 [H_s2 H4]". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil w64 ) by reflexivity. simpl.
        iDestruct "H_s2" as "[H1_s2 H2_s2]". iMod (own_slice_small_persist with "[$H1_s2]") as "H1_s2".
        wp_pures. wp_load. wp_pures. replace (s2, (#msg .(Message.C2S_Client_Data), #()))%V with (to_val (s2, msg .(Message.C2S_Client_Data))) by reflexivity.
        iDestruct "H6" as "(%t2_ops & H6 & H_t2_ops)". wp_apply (wp_sortedInsert with "[$H6 $H_t2_ops H1_s2]").
        { instantiate (1 := {| Operation.VersionVector := (<[uint.nat s .(Server.Id):=w64_word_instance .(word.add) x (W64 1)]> s .(Server.VectorClock)); Operation.Data := msg .(Message.C2S_Client_Data); |}). apply list_lookup_total_correct in H_x. subst x. unfold lookup_total. iFrame. rewrite length_insert. iPureIntro. repeat (split; try done); try tauto. simpl. eapply Forall_insert; try tauto. change (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) with (s.(Server.VectorClock) !!! uint.nat s.(Server.Id)). rewrite bool_decide_eq_true in H_OBS1. unfold u64_le_CONSTANT in *. rewrite -> CONSTANT_unfold in *. word. } iIntros "%s3 (H_s3 & %H1_sorted)".
        wp_pures. wp_apply (wp_storeField_struct with "[H_s1]"). { repeat econstructor; eauto. } { iExact "H_s1". } iIntros "H_s1".
        wp_pures. wp_load. wp_pures. wp_apply wp_NewSlice. rewrite SessionPrelude.replicate_nil; trivial. iIntros "%s4 H_s4". wp_apply (wp_SliceAppendSlice with "[H4 H_s4]"). { repeat econstructor; eauto. } { instantiate (5 := @nil u64). iSplitR "H4"; try done. }
        iDestruct "H7" as "(%t1_ops & H7 & H_t1_ops)". clear s4. iIntros "%s4 H_s4". iDestruct "H_s4" as "[[H1_s4 H1_s4'] H2_s4]". iMod (own_slice_small_persist with "[$H1_s4]") as "H1_s4".
        wp_load. wp_pures. replace (s4, (#msg .(Message.C2S_Client_Data), #()))%V with (to_val (s4, msg .(Message.C2S_Client_Data))) by reflexivity. simpl.
        wp_apply (wp_sortedInsert with "[H7 H_t1_ops H1_s4]").
        { iSplitL "H7 H_t1_ops".
          - iExists t1_ops. iFrame.
          - instantiate (1 := {| Operation.VersionVector := (<[uint.nat s .(Server.Id):=w64_word_instance .(word.add) x (W64 1)]> s .(Server.VectorClock)); Operation.Data := msg .(Message.C2S_Client_Data); |}). simpl. iSplitL "H1_s4".
            + iFrame. iSplitL "". { iPureIntro. simpl; trivial. }
              simpl. iPureIntro; split. { rewrite length_insert. tauto. } { eapply Forall_insert; try tauto. rewrite bool_decide_eq_true in H_OBS1. red. word. }
            + done.
        }
        iIntros "%s5 (H_s5 & %H2_sorted)". wp_apply (wp_storeField_struct with "[H_s1]"). { repeat econstructor; eauto. } { iExact "H_s1". } iIntros "H_s1".
        wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
        wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
        wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
        wp_pures. wp_load. wp_apply (wp_NewSlice). iIntros "%s6 H_s6". rewrite SessionPrelude.replicate_nil; trivial.
        wp_pures. wp_apply (wp_SliceAppendSlice with "[$H_s6 $H2_s4]"); eauto. clear s6. iIntros "%s6 [H_s6 H4]".
        wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
        wp_pures. wp_load. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
        wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"); eauto. simpl. iIntros "H_reply".
        wp_pures. wp_load. wp_pures. wp_load. wp_pures.
        iModIntro.
        pose (b := true).
        set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, s3, s5, t0, t)).
        set (nm := (W64 4, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 1, W64 0, s6, s .(Server.Id), msg .(Message.C2S_Client_Id))).
        replace (Φ (#true, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (s3, (s5, (t0, (t, #())))))))), (#(W64 4), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (#(W64 1), (#(W64 0), (s6, (#s .(Server.Id), (#msg .(Message.C2S_Client_Id), #())))))))))))))))))))%V) with (Φ (#b, server_val ns, message_val nm)%V) by f_equal.
        unfold server_val, message_val. iApply "HΦ". subst b ns nm. simpl.
        unfold coq_processClientRequest; rewrite Heqb; simpl.
        assert ((uint.Z msg .(Message.C2S_Client_OperationType) =? 0) = false) as H_OBS3.
        { rewrite Z.eqb_neq. word. }
        simpl. rewrite H_OBS3; simpl. rewrite H_x; simpl. replace (replicate (uint.nat (W64 0)) (W64 0)) with ( @nil w64) in * by reflexivity. simpl in *.
        unfold is_message; simplNotation; simpl. rewrite Z.eqb_neq in H_OBS3. replace ((uint.Z x <=? CONSTANT - 1) && (length s .(Server.MyOperations) <=? CONSTANT - 1)) with true; cycle 1.
        { symmetry. rewrite andb_true_iff. split.
          - rewrite bool_decide_eq_true in H_OBS1. rewrite Z.leb_le. word.
          - rewrite bool_decide_eq_true in H_OBS2. rewrite Z.leb_le. word.
        }
        iSplitL "". { done. }
        iSplitL "H3 H4 H_s3 H_s5 H8 H9".
        { apply list_lookup_total_correct in H_x. subst x. unfold lookup_total.
          replace (w64_word_instance .(word.add) (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) (W64 1)) with (W64 (uint.Z (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) + 1)) in * by word.
          iFrame; simpl; simplNotation. repeat rewrite length_insert. repeat (iSplit; try done); iPureIntro; try tauto. eapply Forall_insert; try tauto. red. change (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) with (s.(Server.VectorClock) !!! uint.nat s.(Server.Id)). rewrite bool_decide_eq_true in H_OBS1. word.
        }
        repeat rewrite length_insert.
        iSplitL "H_s6".
        { apply list_lookup_total_correct in H_x. subst x. unfold lookup_total.
          replace (w64_word_instance .(word.add) (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) (W64 1)) with (W64 (uint.Z (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) + 1)) by word.
          repeat (iSplit; try done). iSplitL "". { iApply own_slice_small_nil; eauto. }
          repeat (iSplit; try done). iSplitL "".
          { iExists []. iSplit.
            - iApply own_slice_nil; eauto.
            - simpl. done.
          }
          repeat (iSplit; try done); simpl.
          - iApply (own_slice_to_small with "[$H_s6]").
          - iPureIntro; tauto.
          - iPureIntro; eapply Forall_insert; try tauto. red. change (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) with (s.(Server.VectorClock) !!! uint.nat s.(Server.Id)). rewrite bool_decide_eq_true in H_OBS1. word.
        }
        iSplitL "H20 H27 H16".
        { iFrame. done. }
        apply list_lookup_total_correct in H_x. subst x. unfold lookup_total in *.
        replace (w64_word_instance .(word.add) (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) (W64 1)) with (W64 (uint.Z (list_lookup_total (uint.nat s .(Server.Id)) s .(Server.VectorClock)) + 1)) in * by word.
        iPureIntro. split; simpl; try tauto. split; simpl; trivial. rewrite length_insert; word.
  Qed.

  #[local] Opaque CoqSessionServer.processClientRequest.

  Lemma wp_processRequest sv s msgv msg (n: nat) len_ga len_s2c :
    {{{
        is_server sv s n n n n n len_ga ∗
        is_message msgv msg n n len_s2c ∗
        ⌜SERVER_INVARIANT (fun _s => True) s⌝
    }}}
      CoqSessionServer.processRequest (server_val sv) (message_val msgv)
    {{{
        ns nms, RET (server_val ns, slice_val nms);
        is_server ns (coq_processRequest s msg).1 n n n n n len_ga ∗
        message_slice nms (coq_processRequest s msg).2 n 0%nat ∗
        ⌜SERVER_INVARIANT (fun _s => True) (coq_processRequest s msg).1⌝
    }}}.
  Proof.
    (* unfold is_server. rewrite redefine_server_val redefine_message_val. TypeVector.des sv. TypeVector.des msgv. iIntros "%Φ (H_server & H_message & %H_precondition) HΦ".
    iDestruct "H_server" as "(%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10)".
    iDestruct "H_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & %H19 & H20 & %H21 & %H22 & %H23 & %H24 & %H25 & %H26 & H27 & %H28 & %H29 & %H30)".
    destruct H_precondition as [? ? ? ?]; simplNotation; subst; rewrite /CoqSessionServer.processRequest.
    wp_pure. wp_apply wp_NewSlice. simpl. rewrite SessionPrelude.replicate_nil; cycle 1. { word. } iIntros "%s1 H_s1".
    wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%outGoingRequests H_outGoingRequests".
    wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%server H_server".
    wp_if_destruct.
    { wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%succeeded H_succeeded".
      wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%reply H_reply".
      wp_pures. wp_load. replace (processClientRequest (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #()))))))))%V (#msg .(Message.MessageType), (#msg .(Message.C2S_Client_Id), (#msg .(Message.C2S_Server_Id), (#msg .(Message.C2S_Client_OperationType), (#msg .(Message.C2S_Client_Data), (t7, (#msg .(Message.S2S_Gossip_Sending_ServerId), (#msg .(Message.S2S_Gossip_Receiving_ServerId), (t6, (#msg .(Message.S2S_Gossip_Index), (#msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Index), (#msg .(Message.S2C_Client_OperationType), (#msg .(Message.S2C_Client_Data), (t5, (#msg .(Message.S2C_Server_Id), (#msg .(Message.S2C_Client_Number), #()))))))))))))))))))%V) with (processClientRequest (server_val (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)) (message_val (msg .(Message.MessageType), msg .(Message.C2S_Client_Id), msg .(Message.C2S_Server_Id), msg .(Message.C2S_Client_OperationType), msg .(Message.C2S_Client_Data), t7, msg .(Message.S2S_Gossip_Sending_ServerId), msg .(Message.S2S_Gossip_Receiving_ServerId), t6, msg .(Message.S2S_Gossip_Index), msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Index), msg .(Message.S2C_Client_OperationType), msg .(Message.S2C_Client_Data), t5, msg .(Message.S2C_Server_Id), msg .(Message.S2C_Client_Number)))) by f_equal.
      wp_apply (wp_processClientRequest (OWN_UnsatisfiedRequests := true) with "[H3 H4 H6 H7 H8 H9 H16 H20 H27]"). { iFrame. simplNotation; subst. done. } iIntros "%b %ns %nm (-> & H_server' & H_message' & H_message & %H1_postcondition & %H2_postcondition & %H3_postcondition & %H4_postcondition)".
      wp_store. wp_store. wp_pures; lazymatch goal with [ |- envs_entails _ (wp ?s ?E (App ?k ?e)%E ?Q) ] => eapply (tac_wp_store_ty _ _ _ _ _ _ [AppRCtx k]%list); [repeat econstructor; eauto | tc_solve | let l := reply in iAssumptionCore | reflexivity | simpl] end.
      wp_pures. wp_load. wp_if_destruct.
      - wp_load. wp_load. replace message_val with (message_into_val .(to_val)) by reflexivity. wp_apply (wp_SliceAppend with "[$H_s1]"). iIntros "%s2 H_s2".
        wp_store. wp_load. wp_load. wp_pures. simpl. iModIntro. iApply "HΦ".
        unfold coq_processRequest; rewrite Heqb; replace (uint.nat (W64 0)) with 0%nat by reflexivity. destruct (coq_processClientRequest s msg) as [[succeeded_v s_v] reply_v] eqn: H_OBS; simpl in *.
        subst succeeded_v; simpl in *. iFrame. simpl. done.
      - wp_load. wp_pures. iDestruct "H_server'" as "(%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10)". rename H17 into H17'. iDestruct "H_message'" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & %H19 & H20 & %H21 & %H22 & %H23 & %H24 & %H25 & %H26 & H27 & %H28 & %H29 & %H30)". simplNotation; subst.
        replace (#msg .(Message.MessageType), (#msg .(Message.C2S_Client_Id), (#msg .(Message.C2S_Server_Id), (#msg .(Message.C2S_Client_OperationType), (#msg .(Message.C2S_Client_Data), (t7, (#msg .(Message.S2S_Gossip_Sending_ServerId), (#msg .(Message.S2S_Gossip_Receiving_ServerId), (t6, (#msg .(Message.S2S_Gossip_Index), (#msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Index), (#msg .(Message.S2C_Client_OperationType), (#msg .(Message.S2C_Client_Data), (t5, (#msg .(Message.S2C_Server_Id), (#msg .(Message.S2C_Client_Number), #()))))))))))))))))))%V with (message_into_val .(to_val) (msg .(Message.MessageType), msg .(Message.C2S_Client_Id), msg .(Message.C2S_Server_Id), msg .(Message.C2S_Client_OperationType), msg .(Message.C2S_Client_Data), t7, msg .(Message.S2S_Gossip_Sending_ServerId), msg .(Message.S2S_Gossip_Receiving_ServerId), t6, msg .(Message.S2S_Gossip_Index), msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Index), msg .(Message.S2C_Client_OperationType), msg .(Message.S2C_Client_Data), t5, msg .(Message.S2C_Server_Id), msg .(Message.S2C_Client_Number))) by reflexivity.
        iDestruct "H3" as "(%ops1 & H3 & H_ops1)". wp_apply (wp_SliceAppend with "[$H3]"). iIntros "%s2 H_s2". wp_apply (wp_storeField_struct with "[H_server]"); auto. iIntros "H_server".
        wp_pures. wp_load. wp_load. wp_pures. iModIntro. red in ns, nm. simpl in ns, nm. replace (Φ (#ns.1.1.1.1.1.1.1, (#ns.1.1.1.1.1.1.2, (s2, (ns.1.1.1.1.2, (ns.1.1.1.2, (ns.1.1.2, (ns.1.2, (ns.2, #()))))))), s1)%V) with (Φ (server_val (ns.1.1.1.1.1.1.1, ns.1.1.1.1.1.1.2, s2, ns.1.1.1.1.2, ns.1.1.1.2, ns.1.1.2, ns.1.2, ns.2)%core, s1)%V) by reflexivity. iApply "HΦ".
        unfold coq_processRequest; rewrite Heqb; replace (uint.nat (W64 0)) with 0%nat by reflexivity. do 7 destruct ns as [ns ?]; simpl in *. do 17 destruct nm as [nm ?]; simpl in *. subst.
        destruct (coq_processClientRequest s msg) as [[b s'] msg'] eqn: H_OBS; simpl in *. rewrite Heqb0; simpl. iFrame; simplNotation; simpl. iSplitR ""; try done. iSplit; try done; iPureIntro. destruct H1_postcondition as [? ? ? ?]; split; simpl; trivial.
    }
    wp_if_destruct.
    { wp_load. replace (receiveGossip (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #()))))))))%V (#msg .(Message.MessageType), (#msg .(Message.C2S_Client_Id), (#msg .(Message.C2S_Server_Id), (#msg .(Message.C2S_Client_OperationType), (#msg .(Message.C2S_Client_Data), (t7, (#msg .(Message.S2S_Gossip_Sending_ServerId), (#msg .(Message.S2S_Gossip_Receiving_ServerId), (t6, (#msg .(Message.S2S_Gossip_Index), (#msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Index), (#msg .(Message.S2C_Client_OperationType), (#msg .(Message.S2C_Client_Data), (t5, (#msg .(Message.S2C_Server_Id), (#msg .(Message.S2C_Client_Number), #()))))))))))))))))))%V) with (receiveGossip (server_val (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)) (message_val( msg .(Message.MessageType), msg .(Message.C2S_Client_Id), msg .(Message.C2S_Server_Id), msg .(Message.C2S_Client_OperationType), msg .(Message.C2S_Client_Data), t7, msg .(Message.S2S_Gossip_Sending_ServerId), msg .(Message.S2S_Gossip_Receiving_ServerId), t6, msg .(Message.S2S_Gossip_Index), msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), msg .(Message.S2S_Acknowledge_Gossip_Index), msg .(Message.S2C_Client_OperationType), msg .(Message.S2C_Client_Data), t5, msg .(Message.S2C_Server_Id), msg .(Message.S2C_Client_Number)))) by f_equal.
      wp_apply (wp_receiveGossip with "[H3 H4 H6 H7 H8 H9 H16 H20 H27]"). { iFrame. simplNotation; subst. done. } iIntros "%r (Hr & H_message & [%H1_sorted %H2_sorted] & [%H_ServerMyOperations %H_ServerId])".
      wp_store. wp_load. wp_load. TypeVector.des r. replace (#(W64 2), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (#r, (#msg .(Message.S2S_Gossip_Sending_ServerId), (#msg .(Message.S2S_Gossip_Index), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V with (message_into_val .(to_val) (W64 2, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, r, msg .(Message.S2S_Gossip_Sending_ServerId), msg .(Message.S2S_Gossip_Index), W64 0, W64 0, Slice.nil, W64 0, W64 0)) by reflexivity.
      wp_apply (wp_SliceAppend with "[$H_s1]"). iIntros "%s2 H_s2". wp_store. wp_pures. wp_apply (wp_ref_to); auto. iIntros "%i H_i". wp_apply (wp_ref_to). { repeat econstructor; eauto. } iIntros "%reply H_reply". wp_pures. wp_apply (wp_ref_to); auto. iIntros "%succeeded H_succeeded". wp_pures. simpl in *.
      rename r into Id, w into NumberOfServers, t13 into UnsatisfiedRequests, t12 into VectorClock, t11 into OperationsPerformed, t10 into MyOperations, t9 into PendingOperations, t8 into GossipAcknowledgements.
      set (focus := (coq_receiveGossip s msg).(Server.UnsatisfiedRequests)).
      set (loop_init := (0%nat, (coq_receiveGossip s msg, [Message.mk 2 0 0 0 0 [] 0 0 [] 0 ((coq_receiveGossip s msg).(Server.Id)) (msg.(Message.S2S_Gossip_Sending_ServerId)) (msg.(Message.S2S_Gossip_Index)) 0 0 [] 0 0]))).
      set (loop_step := λ acc : nat * (Server.t * list Message.t), λ element : Message.t,
        let '(i, (s, outGoingRequests)) := acc in
        let '(succeeded, s, reply) := coq_processClientRequest s element in
        if succeeded then
          let UnsatisfiedRequests := coq_deleteAtIndexMessage s.(Server.UnsatisfiedRequests) i in
          (i, (Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), outGoingRequests ++ [reply]))
        else
          ((i + 1)%nat, (s, outGoingRequests))
      ).
      set (n := length s .(Server.VectorClock)). rename s into s0. iDestruct "Hr" as "(%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10)"; simplNotation; simpl in *.
      wp_apply (wp_forBreak_cond
        ( λ continue, ∃ prevs : list Message.t, ∃ nexts : list Message.t, ∃ s : Server.t, ∃ msgs : list Message.t, ∃ out_going_requests : Slice.t, ∃ index : nat, ∃ msgv : tuple_of [u64,u64,u64,u64,u64,Slice.t,u64,u64,Slice.t,u64,u64,u64,u64,u64,u64,Slice.t,u64,u64], ∃ b : bool, ∃ Id : w64, ∃ NumberOfServers : w64, ∃ UnsatisfiedRequests : Slice.t, ∃ VectorClock : Slice.t, ∃ OperationsPerformed : Slice.t, ∃ MyOperations : Slice.t, ∃ PendingOperations : Slice.t, ∃ GossipAcknowledgements : Slice.t,
          ⌜focus = prevs ++ nexts⌝ ∗
          ⌜(index, (s, msgs)) = fold_left loop_step prevs loop_init⌝ ∗
          outGoingRequests ↦[(slice.T (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * (slice.T (slice.T uint64T * (uint64T * unitT)) * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * unitT)))))))))))))))))))%ht] slice_val out_going_requests ∗
          i ↦[uint64T] #index ∗
          reply ↦[(uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * (slice.T (slice.T uint64T * (uint64T * unitT)) * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * unitT))))))))))))))))))%ht] message_val msgv ∗
          succeeded ↦[boolT] #b ∗
          server ↦[(uint64T * (uint64T * (slice.T (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * (slice.T (slice.T uint64T * (uint64T * unitT)) * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * unitT)))))))))))))))))) * (slice.T uint64T * (slice.T (slice.T uint64T * (uint64T * unitT)) * (slice.T (slice.T uint64T * (uint64T * unitT)) * (slice.T (slice.T uint64T * (uint64T * unitT)) * (slice.T uint64T * unitT))))))))%ht] server_val (Id, NumberOfServers, UnsatisfiedRequests, VectorClock, OperationsPerformed, MyOperations, PendingOperations, GossipAcknowledgements)%core ∗
          message_slice UnsatisfiedRequests s.(Server.UnsatisfiedRequests) n n ∗
          own_slice_small VectorClock uint64T (DfracOwn 1) s.(Server.VectorClock) ∗
          operation_slice OperationsPerformed s.(Server.OperationsPerformed) n ∗
          operation_slice MyOperations s.(Server.MyOperations) n ∗
          operation_slice PendingOperations s.(Server.PendingOperations) n ∗
          own_slice_small GossipAcknowledgements uint64T (DfracOwn 1) s.(Server.GossipAcknowledgements) ∗
          message_slice out_going_requests msgs n 0%nat ∗
          ⌜SERVER_INVARIANT s⌝ ∗
          ⌜length s.(Server.UnsatisfiedRequests) = (index + length nexts)%nat⌝ ∗
          ⌜drop index s.(Server.UnsatisfiedRequests) = nexts⌝ ∗
          ⌜length s.(Server.VectorClock) = length s0.(Server.VectorClock)⌝ ∗
          ⌜(index <= uint.nat UnsatisfiedRequests.(Slice.sz))%nat⌝ ∗
          ⌜length s.(Server.UnsatisfiedRequests) = uint.nat UnsatisfiedRequests.(Slice.sz)⌝ ∗
          ⌜Id = s.(Server.Id)⌝ ∗
          ⌜NumberOfServers = s.(Server.NumberOfServers)⌝ ∗
          ⌜length (coq_receiveGossip s0 msg).(Server.GossipAcknowledgements) = length s.(Server.GossipAcknowledgements)⌝ ∗
          ⌜continue = false -> nexts = []⌝
        )%I
      with "[] [H_outGoingRequests H_server H3 H4 H6 H7 H8 H9 H_message H_s2 H_i H_reply H_succeeded]").
      { subst Id NumberOfServers. clear Φ UnsatisfiedRequests VectorClock OperationsPerformed MyOperations PendingOperations GossipAcknowledgements.
        iIntros "%Φ". iModIntro. iIntros "(%prevs & %nexts & %s & %msgs & %out_going_requests & %index & %msgv & %b & %Id & %NumberOfServers & %UnsatisfiedRequests & %VectorClock & %OperationsPerformed & %MyOperations & %PendingOperations & %GossipAcknowledgements & %FOCUS & %LOOP & H_outGoingRequests & H_i & H_reply & H_succeeded & H_server & H_UnsatisfiedRequests & H_VectorClock & H_OperationsPerformed & H_MyOperations & H_PendingOperations & H_GossipAcknowledgements & H_out_going_requests & %H_server_invariant & %claim1 & %claim2 & %claim3 & %claim4 & %claim5 & %claim6 & %claim7 & %LENGTH_GossipAcknowledgements & %H_continue) HΦ". iDestruct "H_UnsatisfiedRequests" as "(%msgv1 & [H1_UnsatisfiedRequests H2_UnsatisfiedRequests] & H3_UnsatisfiedRequests)".
        wp_load. wp_load. wp_apply (wp_slice_len). wp_if_destruct.
        - wp_pures. wp_load. wp_pures. wp_load. wp_pures.
          iPoseProof (big_sepL2_length with "[$H3_UnsatisfiedRequests]") as "%YES1".
          iPoseProof (own_slice_small_sz with "[$H1_UnsatisfiedRequests]") as "%YES2".
          assert (is_Some (msgv1 !! uint.nat (W64 index))) as [e H_e].
          { eapply lookup_lt_is_Some_2. word. }
          assert (length nexts > 0)%nat as NE_NIL.
          { apply f_equal with (f := length) in FOCUS. rewrite length_app in FOCUS. word. }
          destruct nexts as [ | cur nexts].
          { simpl in NE_NIL. word. }
          clear NE_NIL H_continue.
          iPoseProof (big_sepL2_middle_split _ H_e with "[$H3_UnsatisfiedRequests]") as "(%cur' & %prevs' & %nexts' & [%EQ %H_cur'] & [%len_s2c' is_message_cur'] & message_slice_prevs' & message_slice_nexts')".
          wp_apply (wp_SliceGet with "[$H1_UnsatisfiedRequests]"). { iPureIntro. exact H_e. } iIntros "H1_UnsatisfiedRequests".
          wp_load. wp_apply (wp_processClientRequest (OWN_UnsatisfiedRequests := false) with "[H_VectorClock H_OperationsPerformed H_MyOperations H_PendingOperations H_GossipAcknowledgements is_message_cur']").
          { iSplitR "is_message_cur'".
            - iFrame; simplNotation; done.
            - iSplitL "is_message_cur'".
              + iExact "is_message_cur'".
              + iPureIntro; done.
          }
          iIntros "%r %ns %nm (-> & is_server_ns & is_message_nm & is_message_cur' & %H1_invariant & %H2_invariant & %H3_invariant & %H4_invariant)". wp_store. wp_store. wp_pures; lazymatch goal with [ |- envs_entails _ (wp ?s ?E (App ?k ?e)%E ?Q) ] => eapply (tac_wp_store_ty _ _ _ _ _ _ [AppRCtx k]%list); [repeat econstructor; eauto | tc_solve | let l := reply in iAssumptionCore | reflexivity | simpl] end. wp_load. wp_if_destruct.
          + wp_load. wp_load. iDestruct "H_out_going_requests" as "(%ops1 & H_out_going_requests & H_ops1)". replace (message_val nm) with (message_into_val.(to_val) nm) by reflexivity. wp_apply (wp_SliceAppend with "[$H_out_going_requests]"). iIntros "%out_going_requests' H_out_goint_requests'".
            wp_store. wp_load. wp_load. wp_pures. TypeVector.des ns; simplNotation; subst t13. wp_apply (wp_deleteAtIndexMessage with "[$H1_UnsatisfiedRequests $H2_UnsatisfiedRequests message_slice_prevs' message_slice_nexts' is_message_cur']").
            { instantiate (1 := (prevs' ++ cur' :: nexts')%list). iSplitR "".
              - iApply (big_sepL2_middle_merge with "[is_message_cur' $message_slice_prevs' $message_slice_nexts']"); eauto.
              - iPureIntro; rewrite length_app; simpl; word.
            }
            iIntros "%ns2 [message_slice_ns2 %LEN_ns2]". wp_apply (wp_storeField_struct with "[H_server]"). { repeat econstructor; eauto. } { iExact "H_server". } iIntros "H_server". wp_pures. iModIntro. iApply "HΦ". simpl in *.
            assert (length prevs' = index) as claim8 by word.
            assert (cur = cur' /\ nexts = nexts') as [<- <-].
            { enough (cur :: nexts = cur' :: nexts') by now split; congruence.
              rewrite <- claim2. rewrite EQ. rewrite drop_app.
              replace (drop index prevs') with ( @nil Message.t) by now symmetry; eapply nil_length_inv; rewrite length_drop; word.
              replace (index - length prevs')%nat with 0%nat by word.
              reflexivity.
            }
            iAssert ⌜(length (coq_deleteAtIndexMessage s .(Server.UnsatisfiedRequests) index) = uint.nat ns2 .(Slice.sz))%nat⌝%I as "%ns2_SZ".
            { iDestruct "message_slice_ns2" as "(%ops2 & message_slice_ns2 & H_ops2)".
              iPoseProof (big_sepL2_length with "[$H_ops2]") as "%LEN1".
              iPoseProof (own_slice_sz with "[$message_slice_ns2]") as "%LEN2".
              rewrite <- EQ in LEN1. rewrite <- LEN2. iPureIntro. symmetry. replace (uint.nat (W64 index)) with index in LEN1 by word. done.
            }
            iExists (prevs ++ [cur]). iExists nexts. iExists (let s : Server.t := (coq_processClientRequest s cur).1.2 in Server.mk s.(Server.Id) s.(Server.NumberOfServers) (coq_deleteAtIndexMessage s.(Server.UnsatisfiedRequests) index) s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements)). iExists (msgs ++ [(coq_processClientRequest s cur).2])%list. iExists _. iExists index. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iFrame.
            iSplitL "". { rewrite <- app_assoc. done. }
            iSplitL "". { iPureIntro. rewrite fold_left_app. simpl. rewrite <- LOOP. simpl. destruct (coq_processClientRequest s cur) as [[b' s'] reply']; simpl in *. subst b'. replace (uint.nat (W64 index)) with index by word. reflexivity. }
            iSplitL "message_slice_ns2". { simpl. rewrite <- EQ. replace (uint.nat (W64 index)) with index by word. rewrite <- H2_invariant. iExact "message_slice_ns2". }
            simpl in *. iDestruct "is_server_ns" as "(%H1'' & %H2'' & H3'' & H4'' & %H5'' & H6'' & H7'' & H8'' & H9'' & %H10'')". iFrame. iPureIntro.
            simplNotation; subst; simpl; split. { destruct H1_invariant. split; simpl; trivial. } rewrite <- EQ in LEN_ns2. replace (uint.nat (W64 (length prevs'))) with (length prevs') in * by word. repeat (split; try done).
            * rewrite <- H2_invariant. word.
            * unfold coq_deleteAtIndexMessage. rewrite <- H2_invariant. rewrite <- drop_drop. replace (uint.nat (W64 (length prevs'))) with (length prevs') in * by word. rewrite -> claim2. simpl. replace (drop 0 nexts) with nexts by reflexivity. rewrite drop_app.
              replace (drop (length prevs') (take (length prevs') s .(Server.UnsatisfiedRequests))) with ( @nil Message.t) by now symmetry; eapply nil_length_inv; rewrite length_drop; rewrite length_take; word.
              replace (length prevs' - length (take (length prevs') s .(Server.UnsatisfiedRequests)))%nat with 0%nat by now rewrite length_take; word.
              reflexivity.
            * word.
            * rewrite <- H2_invariant. word.
          + TypeVector.des ns; simplNotation; subst t13.
            assert (length prevs' = index) as claim8 by word.
            assert (cur = cur' /\ nexts = nexts') as [<- <-].
            { enough (cur :: nexts = cur' :: nexts') by now split; congruence.
              rewrite <- claim2. rewrite EQ. rewrite drop_app.
              replace (drop index prevs') with ( @nil Message.t) by now symmetry; eapply nil_length_inv; rewrite length_drop; word.
              replace (index - length prevs')%nat with 0%nat by word.
              reflexivity.
            }
            wp_load. wp_store. iModIntro. iApply "HΦ".
            iExists (prevs ++ [cur])%list. iExists nexts. iExists ((coq_processClientRequest s cur).1.2). iExists msgs. iExists _. iExists (index + 1)%nat. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. replace (w64_word_instance .(word.add) (W64 index) (W64 1)) with (W64 (index + 1)%nat) by word. iFrame.
            iSplitL "". { rewrite <- app_assoc. done. }
            iSplitL "". { iPureIntro. rewrite fold_left_app. simpl. rewrite <- LOOP. simpl. destruct (coq_processClientRequest s cur) as [[b' s'] reply']; simpl in *. subst b'; reflexivity. }
            iSplitL "message_slice_prevs' message_slice_nexts' is_message_cur'". { replace (uint.nat (W64 index)) with index in H_e |- * by word. rewrite <- H2_invariant, -> EQ. iApply (big_sepL2_middle_merge with "[is_message_cur' $message_slice_prevs' $message_slice_nexts']"); eauto. }
            simpl in *. iDestruct "is_server_ns" as "(%H1'' & %H2'' & H3'' & H4'' & %H5'' & H6'' & H7'' & H8'' & H9'' & %H10'')". iFrame. iPureIntro.
            simplNotation; subst; simpl; split. { destruct H1_invariant. split; simpl; trivial. } repeat (split; try done).
            * rewrite <- H2_invariant. apply f_equal with (f := length) in EQ. rewrite length_app in EQ. simpl in *. word.
            * rewrite <- drop_drop. rewrite <- H2_invariant. rewrite -> claim2. simpl. replace (drop 0 nexts) with nexts by reflexivity. reflexivity.
            * word.
            * rewrite <- H2_invariant. word.
        - iModIntro. iApply "HΦ".
          iExists prevs. iExists nexts. iExists s. iExists msgs. iExists _. iExists index. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iExists _. iFrame. iPureIntro.
          simplNotation; subst; simpl; split. { trivial. } repeat (split; try done). intros _.
          eapply nil_length_inv. word.
      }
      { iAssert ⌜length (coq_receiveGossip s0 msg) .(Server.UnsatisfiedRequests) = uint.nat UnsatisfiedRequests .(Slice.sz)⌝%I as "%UnsatisfiedRequests_SZ".
        { iDestruct "H3" as "(%ops1 & H3 & Hops1)". iPoseProof (big_sepL2_length with "[$Hops1]") as "%LEN1". iPoseProof (own_slice_sz with "[$H3]") as "%LEN2". word. }
        iExists []. iExists focus. iExists (coq_receiveGossip s0 msg). iExists [Message.mk 2 0 0 0 0 [] 0 0 [] 0 ((coq_receiveGossip s0 msg).(Server.Id)) (msg.(Message.S2S_Gossip_Sending_ServerId)) (msg.(Message.S2S_Gossip_Index)) 0 0 [] 0 0]. iExists s2. iExists 0%nat. iExists (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0). iExists false. iExists Id. iExists NumberOfServers. iExists UnsatisfiedRequests. iExists VectorClock. iExists OperationsPerformed. iExists MyOperations. iExists PendingOperations. iExists GossipAcknowledgements. iFrame.
        iSplitL "". { done. }
        iSplitL "". { simpl. done. }
        iSplitL "".
        { simpl. iSplitR ""; eauto. iExists 0%nat. repeat (iSplit; try done); simplNotation.
          iSplitL "". { iApply own_slice_small_nil; eauto. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { iExists []; iSplit; simpl; try done; iApply own_slice_nil; eauto. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { iApply own_slice_small_nil; eauto. }
          done.
        }
        iPureIntro. split.
        { split; trivial.
          - rewrite <- H_ServerMyOperations; trivial.
          - rewrite <- H_ServerId; word.
        }
        split. { unfold focus. word. }
        split. { unfold focus. reflexivity. }
        split. { word. }
        split. { word. }
        split. { eauto. }
        split. { word. }
        split. { word. }
        split. { word. }
        congruence.
      }
      { subst. clear UnsatisfiedRequests VectorClock OperationsPerformed MyOperations PendingOperations GossipAcknowledgements. iIntros "(%prevs & %nexts & %s & %msgs & %out_going_requests & %index & %msgv & %b & %Id & %NumberOfServers & %UnsatisfiedRequests & %VectorClock & %OperationsPerformed & %MyOperations & %PendingOperations & %GossipAcknowledgements & %FOCUS & %LOOP & H_outGoingRequests & H_i & H_reply & H_succeeded & H_server & H_UnsatisfiedRequests & H_VectorClock & H_OperationsPerformed & H_MyOperations & H_PendingOperations & H_GossipAcknowledgements & H_out_going_requests & %H_server_invariant & %claim1 & %claim2 & %claim3 & %claim4 & %claim5 & %claim6 & %claim7 & %LENGTH_GossipAcknowledgements & %H_continue)". iDestruct "H_UnsatisfiedRequests" as "(%msgv1 & [H1_UnsatisfiedRequests H2_UnsatisfiedRequests] & H3_UnsatisfiedRequests)".
        specialize (H_continue eq_refl). subst nexts. rewrite H_continue in FOCUS. rewrite app_nil_r in FOCUS. subst prevs.
        wp_load. wp_load. wp_pures. iModIntro. iApply "HΦ".
        iSplitL "H1_UnsatisfiedRequests H2_UnsatisfiedRequests H3_UnsatisfiedRequests H_VectorClock H_OperationsPerformed H_MyOperations H_PendingOperations H_GossipAcknowledgements".
        { iFrame; simplNotation; subst; iFrame. unfold coq_processRequest; rewrite Heqb0; replace (uint.nat (W64 1)) with 1%nat by word; simpl; fold loop_step; fold loop_init; fold focus; rewrite <- LOOP; simpl; iFrame.
          iPureIntro; repeat (split; try done). rewrite H10; trivial.
        } 
        unfold coq_processRequest; rewrite Heqb0; replace (uint.nat (W64 1)) with 1%nat by word; simpl; fold loop_step; fold loop_init; fold focus; rewrite <- LOOP; simpl; iFrame. done.
      }
    }
    wp_if_destruct.
    { wp_load. replace (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #()))))))))%V with (server_val (s.(Server.Id), s.(Server.NumberOfServers), t4, t3, t2, t1, t0, t)) by reflexivity. replace (#msg .(Message.MessageType), (#msg .(Message.C2S_Client_Id), (#msg .(Message.C2S_Server_Id), (#msg .(Message.C2S_Client_OperationType), (#msg .(Message.C2S_Client_Data), (t7, (#msg .(Message.S2S_Gossip_Sending_ServerId), (#msg .(Message.S2S_Gossip_Receiving_ServerId), (t6, (#msg .(Message.S2S_Gossip_Index), (#msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), (#msg .(Message.S2S_Acknowledge_Gossip_Index), (#msg .(Message.S2C_Client_OperationType), (#msg .(Message.S2C_Client_Data), (t5, (#msg .(Message.S2C_Server_Id), (#msg .(Message.S2C_Client_Number), #()))))))))))))))))))%V with (message_val (msg.(Message.MessageType), msg.(Message.C2S_Client_Id), msg.(Message.C2S_Server_Id), msg.(Message.C2S_Client_OperationType), msg.(Message.C2S_Client_Data), t7, msg.(Message.S2S_Gossip_Sending_ServerId), msg.(Message.S2S_Gossip_Receiving_ServerId), t6, msg.(Message.S2S_Gossip_Index), msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId), msg.(Message.S2S_Acknowledge_Gossip_Receiving_ServerId), msg.(Message.S2S_Acknowledge_Gossip_Index), msg.(Message.S2C_Client_OperationType), msg.(Message.S2C_Client_Data), t5, msg.(Message.S2C_Server_Id), msg.(Message.S2C_Client_Number))) by reflexivity.
      wp_apply (wp_acknowledgeGossip (OWN_UnsatisfiedRequests := true) with "[H3 H4 H6 H7 H8 H9 H16 H20 H27]"). { iFrame; simplNotation; simpl. done. } iIntros "[H_is_server H_is_message]". wp_store. wp_load. wp_load. wp_pures.
      iModIntro. iApply "HΦ". unfold coq_processRequest; rewrite Heqb1; replace (uint.nat (W64 2)) with 2%nat by word; simpl; iFrame. iSplitR "".
      - simpl; done.
      - iPureIntro; unfold coq_acknowledgeGossip. destruct (uint.Z msg .(Message.S2S_Acknowledge_Gossip_Sending_ServerId) >=? length s .(Server.GossipAcknowledgements)) as [ | ] eqn: H_OBS; split; trivial.
    }
    wp_if_destruct.
    { wp_apply (wp_ref_to); auto. iIntros "%i H_i". wp_pures.
      set (loop_init := @nil Message.t).
      set (loop_step := λ acc : list Message.t, λ index : u64,
        if negb (uint.nat index =? uint.nat s.(Server.Id))%nat && negb (length (coq_getGossipOperations s index) =? 0)%nat then
          let S2S_Gossip_Sending_ServerId := s.(Server.Id) in
          let S2S_Gossip_Receiving_ServerId := index in
          let S2S_Gossip_Operations := coq_getGossipOperations s index in
          let S2S_Gossip_Index := length (s.(Server.MyOperations)) in
          let message := Message.mk 1 0 0 0 0 [] S2S_Gossip_Sending_ServerId S2S_Gossip_Receiving_ServerId S2S_Gossip_Operations S2S_Gossip_Index 0 0 0 0 0 [] 0 0 in
          acc ++ [message]
        else
          acc
      ).
      iAssert ⌜uint.nat t1.(Slice.sz) = length s .(Server.MyOperations)⌝%I as "%t1_SZ".
      { iDestruct "H7" as "(%ops1 & H7 & H_ops1)". iPoseProof (big_sepL2_length with "[$H_ops1]") as "%LEN1". iPoseProof (own_slice_sz with "[$H7]") as "%LEN2". word. }
      wp_apply (wp_forBreak_cond
        ( λ continue, ∃ index : nat, ∃ msgs : list Message.t, ∃ out_going_requests : Slice.t,
          ⌜msgs = fold_left loop_step (map (λ i : nat, W64 i) (seq 0%nat index)) loop_init⌝ ∗
          i ↦[uint64T] #(W64 index) ∗
          server ↦[(uint64T * (uint64T * (slice.T (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * (slice.T (slice.T uint64T * (uint64T * unitT)) * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * unitT)))))))))))))))))) * (slice.T uint64T * (slice.T (slice.T uint64T * (uint64T * unitT)) * (slice.T (slice.T uint64T * (uint64T * unitT)) * (slice.T (slice.T uint64T * (uint64T * unitT)) * (slice.T uint64T * unitT))))))))%ht] server_val (s.(Server.Id), s.(Server.NumberOfServers), t4, t3, t2, t1, t0, t)%core ∗
          outGoingRequests ↦[(slice.T (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * (slice.T (slice.T uint64T * (uint64T * unitT)) * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (uint64T * (slice.T uint64T * (uint64T * (uint64T * unitT)))))))))))))))))))%ht] slice_val out_going_requests ∗
          message_slice t4 s .(Server.UnsatisfiedRequests) (length s .(Server.VectorClock)) (length s .(Server.VectorClock)) ∗
          own_slice_small t3 uint64T (DfracOwn 1) s .(Server.VectorClock) ∗
          operation_slice t2 s .(Server.OperationsPerformed) (length s .(Server.VectorClock)) ∗
          operation_slice t1 s .(Server.MyOperations) (length s .(Server.VectorClock)) ∗
          operation_slice t0 s .(Server.PendingOperations) (length s .(Server.VectorClock)) ∗
          own_slice_small t uint64T (DfracOwn 1) s .(Server.GossipAcknowledgements) ∗
          own_slice_small t7 uint64T (DfracOwn 1) msg .(Message.C2S_Client_VersionVector) ∗
          operation_slice t6 msg .(Message.S2S_Gossip_Operations) (length s .(Server.VectorClock)) ∗
          own_slice_small t5 uint64T (DfracOwn 1) msg .(Message.S2C_Client_VersionVector) ∗
          message_slice out_going_requests msgs (length s .(Server.VectorClock)) 0%nat ∗
          ⌜index = uint.nat (W64 index) /\ uint.Z (W64 index) ≤ uint.Z s .(Server.NumberOfServers)⌝ ∗
          ⌜continue = false -> index = uint.nat s.(Server.NumberOfServers)⌝
        )%I
      with "[] [H3 H4 H6 H7 H8 H9 H16 H20 H27 H_i H_server H_outGoingRequests H_s1]").
      { clear Φ. iIntros "%Φ". iModIntro. iIntros "(%index & %msgs & %out_going_requests & %H_msgs & H_i & H_server & H_outGoingRequests & H_UnsatisfiedRequests & H_VectorClock & H_OperationsPerformed & H_MyOperations & H_PendingOperations &H_GossipAcknowledgements & H_C2S_Client_VersionVector & H_S2S_Gossip_Operations & H_S2C_Client_VersionVector & H_out_going_requests & [%i_BOUND %i_BOUND'] & %H_continue) HΦ".
        wp_load. wp_if_destruct.
        - wp_load. wp_load. wp_if_destruct.
          + wp_load. wp_load. wp_apply (wp_getGossipOperations (OWN_UnsatisfiedRequests := true) with "[H_UnsatisfiedRequests H_VectorClock H_OperationsPerformed H_MyOperations H_PendingOperations H_GossipAcknowledgements]"). { iFrame; simplNotation; simpl; done. } iIntros "%ns [H_ns H_is_server]".
            replace (coq_getGossipOperations s (uint.nat (W64 index))) with (coq_getGossipOperations s index) in * by now f_equal; word. wp_apply wp_slice_len. wp_if_destruct.
            * wp_load. wp_load. wp_pures. wp_apply wp_slice_len. wp_load. refine (let TMP : w64 := t1 .(Slice.sz) in _). fold TMP. replace (#(W64 1), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (#s .(Server.Id), (#(W64 index), (ns, (#TMP, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V with (message_into_val .(to_val) (W64 1, W64 0, W64 0, W64 0, W64 0, Slice.nil, s.(Server.Id), (W64 index), ns, TMP, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)) by reflexivity. subst TMP.
              iDestruct "H_out_going_requests" as "(%msgv & H_out_going_requests & H_msgv)". wp_apply (wp_SliceAppend with "[$H_out_going_requests]"). iIntros "%out_going_requests' H_out_going_requests'". wp_store. wp_load. wp_store.
              iAssert ⌜uint.nat ns.(Slice.sz) = length (coq_getGossipOperations s index)⌝%I as "%ns_SZ".
              { iDestruct "H_ns" as "(%ops1 & H_ns & H_ops1)". iPoseProof (big_sepL2_length with "[$H_ops1]") as "%LEN1". iPoseProof (own_slice_sz with "[$H_ns]") as "%LEN2". word. }
              iModIntro. iApply "HΦ". iExists (index + 1)%nat. iExists (fold_left loop_step (map (λ i : nat, W64 i) (seq 0 (index + 1))) loop_init). iExists out_going_requests'. replace (w64_word_instance .(word.add) (W64 index) (W64 1)) with (W64 (index + 1)%nat) by word. iFrame.
              iDestruct "H_is_server" as "(%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10)"; simplNotation; simpl; subst; iFrame.
              iSplitL "". { done. }
              iSplitR "".
              { replace (index + 1)%nat with (S index) by word. rewrite seq_S. iPoseProof (big_sepL2_length with "[$H_msgv]") as "%LEN". rewrite map_app; rewrite fold_left_app. simpl. unfold loop_step at 2.
                destruct (uint.nat (W64 index) =? uint.nat s .(Server.Id))%nat as [ | ] eqn: H_OBS2. { rewrite Nat.eqb_eq in H_OBS2. contradiction Heqb4. word. }
                destruct (length (coq_getGossipOperations s (W64 index)) =? 0)%nat as [ | ] eqn: H_OBS3. { rewrite Nat.eqb_eq in H_OBS3. contradiction Heqb5. word. }
                simpl. iApply (big_sepL2_app with "[$H_msgv] [H_ns]"). simpl. iSplitR ""; try done. iExists 0%nat. iFrame; simplNotation; simpl.
                iSplitL "". { done. }
                iSplitL "". { done. }
                iSplitL "". { done. }
                iSplitL "". { done. }
                iSplitL "". { done. }
                iSplitL "". { iApply own_slice_small_nil; eauto. }
                iSplitL "". { done. }
                iSplitL "". { done. }
                iSplitL "". { done. }
                iSplitL "". { iPureIntro. rewrite <- t1_SZ. word. }
                iSplitL "". { done. }
                iSplitL "". { done. }
                iSplitL "". { done. }
                iSplitL "". { done. }
                iSplitL "". { done. }
                iSplitL "". { iApply own_slice_small_nil; eauto. }
                done.
              }
              iPureIntro; split; [word | congruence].
            * wp_load. wp_store.
              iAssert ⌜uint.nat ns.(Slice.sz) = length (coq_getGossipOperations s index)⌝%I as "%ns_SZ".
              { iDestruct "H_ns" as "(%ops1 & H_ns & H_ops1)". iPoseProof (big_sepL2_length with "[$H_ops1]") as "%LEN1". iPoseProof (own_slice_sz with "[$H_ns]") as "%LEN2". word. }
              iModIntro. iApply "HΦ".
              iExists (index + 1)%nat. iExists _. iExists out_going_requests. replace (w64_word_instance .(word.add) (W64 index) (W64 1)) with (W64 (index + 1)%nat) by word. iFrame.
              iDestruct "H_is_server" as "(%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10)"; simplNotation; simpl; subst; iFrame.
              iSplitL "".
              { replace (index + 1)%nat with (S index) by word. rewrite seq_S. rewrite map_app. rewrite fold_left_app. simpl. unfold loop_step at 2. destruct (uint.nat (W64 index) =? uint.nat s .(Server.Id))%nat as [ | ] eqn: H_OBS2.
                - simpl in *. done.
                - destruct (length (coq_getGossipOperations s index) =? 0)%nat as [ | ] eqn: H_OBS3.
                  + simpl in *. done.
                  + rewrite -> Nat.eqb_neq in H_OBS2, H_OBS3. simpl. word.
              }
              iPureIntro; split; [word | congruence].
          + wp_load. wp_store.
            iModIntro. iApply "HΦ".
            iExists (index + 1)%nat. iExists _. iExists out_going_requests. replace (w64_word_instance .(word.add) (W64 index) (W64 1)) with (W64 (index + 1)%nat) by word. iFrame.
            iPureIntro. split.
            * replace (index + 1)%nat with (S index) by word. rewrite seq_S. rewrite map_app. rewrite fold_left_app. simpl. unfold loop_step at 2. destruct (uint.nat index =? uint.nat s .(Server.Id))%nat as [ | ] eqn: H_OBS2.
              { simpl in *. done. }
              destruct (length (coq_getGossipOperations s index) =? 0)%nat as [ | ] eqn: H_OBS3.
              { simpl in *. done. }
              { rewrite -> Nat.eqb_neq in H_OBS2, H_OBS3. simpl. contradiction H_OBS2. rewrite i_BOUND. rewrite Heqb4. word. }
            * split. { word. } congruence.
        - iModIntro. iApply "HΦ".
          iExists index. iExists _. iExists out_going_requests. iFrame.
          iPureIntro; split; trivial. split; try word.
      }
      { iExists 0%nat. iExists _. iExists _. iFrame.
        iSplitL "". { iPureIntro; reflexivity. }
        iSplitL "". { simpl. done. }
        iPureIntro; repeat (split; trivial).
        - word.
        - congruence.
      }
      { iIntros "(%index & %msgs & %out_going_requests & %H_msgs & H_i & H_server & H_outGoingRequests & H_UnsatisfiedRequests & H_VectorClock & H_OperationsPerformed & H_MyOperations & H_PendingOperations &H_GossipAcknowledgements & H_C2S_Client_VersionVector & H_S2S_Gossip_Operations & H_S2C_Client_VersionVector & H_out_going_requests & [%i_BOUND %i_BOUND'] & %H_continue)".
        wp_load. wp_load. wp_pures.
        specialize (H_continue eq_refl). subst index msgs.
        iModIntro. iApply "HΦ".
        unfold coq_processRequest; replace (uint.nat msg.(Message.MessageType)) with 3%nat by word; simpl; fold loop_step; fold loop_init. iFrame; simplNotation; simpl. done.
      }
    }
    { set (ns := (s.(Server.Id), s.(Server.NumberOfServers), t4, t3, t2, t1, t0, t)). replace (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #()))))))))%V with (server_val ns) by reflexivity.
      wp_load. wp_load. wp_pures. iModIntro.
      iApply "HΦ". unfold coq_processRequest. destruct (uint.nat msg .(Message.MessageType)) as [ | [ | [ | [ | n]]]] eqn: H_OBS; try word. iFrame; simplNotation; simpl; iPureIntro.
      split; trivial.
      - split; try done.
      - split; trivial. split; trivial.
    }
  Qed. *) Admitted.

  #[local] Opaque CoqSessionServer.processRequest.

End heap.

#[global] Opaque CoqSessionServer.processClientRequest.
#[global] Opaque CoqSessionServer.processRequest.
