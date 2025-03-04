From Perennial.program_proof.session Require Export session_prelude  coq_session.
From Perennial.program_proof.session Require Export versionVector processClientRequest.

Section heap.
  Context `{hG: !heapGS Σ}.

  (*
  Lemma wp_processClientRequest sv s msgv msg (n: nat) :
    {{{
        is_server sv s n ∗ 
        is_message msgv msg n
    }}}
      processClientRequest (server_val sv) (message_val msgv)
    {{{
        b ns nm , RET (b, server_val ns, message_val nm);
        is_server ns (coq_processClientRequest s msg).1.2 n ∗
        (∃ x, is_message nm (coq_processClientRequest s msg).2 x ∗ ⌜b = #true -> x = n⌝) ∗
        ⌜b = #(coq_processClientRequest s msg).1.1⌝
    }}}.
  Proof.
    iIntros "%Φ (H1 & H2) HΦ".
    iDestruct "H1" as "(%H1 & %H2 & H1 & %H3 & H4 & H5 & H6 & H7 & %H4 & H8)".
    iDestruct "H2" as "(%H5 & %H6 & %H7 & %H8 & %H9 & %H10 & H9 & %H11 & %H12 & H10 & %H13 & %H14 & %H15 & %H16 & %H17 & %H18 & %H19 & H11 & %H20 & %H21)".
    rewrite /processClientRequest. wp_pures.
    wp_apply (wp_ref_to); first repeat apply (@val_ty_pair); auto.
    iIntros (ret) "H2".
    wp_apply (wp_compareVersionVector with "[H4 H9]").
    { iFrame. iPureIntro. rewrite <- H3. rewrite <- H10. auto. }
    iIntros (r) "(-> & H12 & H13 & %H23)".
    wp_if_destruct.
    - wp_pures. wp_load. 
      assert (zero_val uint64T = #(W64 0)) by auto. 
      assert (zero_val (slice.T uint64T) = slice_val Slice.nil) by auto.
      assert (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)) = slice_val Slice.nil) by auto.
      rewrite H H0 H3. unfold message_val.
      assert (message_val ((W64 0), (W64 0), (W64 0), (W64 0), (W64 0), Slice.nil, (W64 0), (W64 0), Slice.nil, (W64 0), (W64 0), (W64 0), (W64 0), (W64 0), (W64 0), Slice.nil, (W64 0), (W64 0))
        = (#(W64 0), (#(W64 0), (#(W64 0), (#(W64 0), (#(W64 0), (Slice.nil, (#(W64 0), (#(W64 0), (Slice.nil, (#(W64 0), (#(W64 0), (#(W64 0), (#(W64 0), (#(W64 0), (#(W64 0), (Slice.nil, (#(W64 0), (#(W64 0), #()))))))))))))))))))%V).
      { unfold message_val. simpl. auto. }
      wp_pures. iModIntro. rewrite <- H22. iApply "HΦ".
      unfold coq_processClientRequest. rewrite -> Heqb. simpl.
      iSplitL "H1 H5 H6 H7 H8 H12".
      { unfold is_server. iFrame. done. }
      iSplitL "H10 H11 H13".
      { iExists 0%nat. unfold is_message. iFrame. simpl.
        iClear "H10". iClear "H11". iClear "H13".
        repeat (iSplitL; [done | ]). iSplit.
        - repeat (iSplitL; [done | ]). iSplitL.
          { iApply own_slice_small_nil; eauto. }
          repeat (iSplitL; [done | ]). iSplitL.
          { iExists []. iSplitL.
            - iApply own_slice_nil; eauto.
            - iApply big_sepL2_nil; eauto.
          }
          repeat (iSplitL; [done | ]). iSplitL.
          { iApply own_slice_small_nil; eauto. }
          done.
        - iPureIntro. congruence.
      }
      done.
    - wp_pures. wp_if_destruct.
      + wp_apply (wp_storeField_struct with "[H2]"); auto. iIntros "H2". wp_pures.
        wp_apply (wp_storeField_struct with "[H2]"); auto. iIntros "H2". wp_pures.
        wp_apply (wp_getDataFromOperationLog with "[H5]"); auto. iIntros "%r [-> H5]".
        wp_apply (wp_storeField_struct with "[H2]"); auto. iIntros "H2". wp_pures.
        wp_apply (wp_storeField_struct with "[H2]"); auto. iIntros "H2". wp_pures.
        wp_apply (wp_storeField_struct with "[H2]"); auto. iIntros "H2". wp_pures.
        wp_apply (wp_storeField_struct with "[H2]"); auto. iIntros "H2". wp_pures.
        wp_load. wp_pures. iModIntro. rewrite H19. rewrite H6. rewrite H1.
        assert (zero_val uint64T = #(W64 0)) by auto. rewrite H. clear H. 
        assert (zero_val (slice.T uint64T) = slice_val Slice.nil) by auto. rewrite H. clear H. 
        assert (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)) = slice_val Slice.nil) by auto. rewrite H. clear H. 
        assert (message_val ((W64 4), (W64 0), (W64 0), (W64 0), (W64 0), Slice.nil, (W64 0), (W64 0), Slice.nil, (W64 0), (W64 0), (W64 0), (W64 0), (W64 0), (coq_getDataFromOperationLog s.(Server.OperationsPerformed)), (sv.1.1.1.1.2), (s .(Server.Id)), (msg .(Message.C2S_Client_Id)))
          = (#(W64 4), (#(W64 0), (#(W64 0), (#(W64 0), (#(W64 0), (Slice.nil, (#(W64 0), (#(W64 0), (Slice.nil, (#(W64 0), (#(W64 0), (#(W64 0), (#(W64 0), (#(W64 0), (#(coq_getDataFromOperationLog s.(Server.OperationsPerformed)), ((sv.1.1.1.1.2), (#(s .(Server.Id)), (#(msg .(Message.C2S_Client_Id)), #()))))))))))))))))))%V).
        { unfold message_val. simpl. auto. }
        rewrite <- H. clear H. iApply "HΦ". unfold coq_processClientRequest.
        destruct (coq_compareVersionVector s .(Server.VectorClock) msg .(Message.C2S_Client_VersionVector)) as [ | ] eqn: H_OBS; simpl in *.
        { destruct (uint.nat msg .(Message.C2S_Client_OperationType) =? 0) as [ | ] eqn: H_OBS'; [rewrite Z.eqb_eq in H_OBS' | rewrite Z.eqb_neq in H_OBS']; simpl in *.
          - iSplitL "H1 H6 H7 H8 H12 H5".
            { iFrame. iPureIntro. (repeat (split; trivial)); word. }
            iSplitR ""; trivial. iExists (length msg .(Message.S2C_Client_VersionVector)). iSplitR ""; trivial.
            iSplitL "". { simpl. done. }
            iSplitL "". { simpl. done. }
            iSplitL "". { simpl. done. }
            iSplitL "". { simpl. done. }
            iSplitL "". { simpl. done. }
            iSplitL "". { simpl. admit. (* stuck! *) }
            admit.
          - admit.
        }
        { admit.
        }
      + admit.
  Admitted. *)

End heap.
