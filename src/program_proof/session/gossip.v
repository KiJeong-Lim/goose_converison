From Perennial.program_proof.session Require Export session_prelude coq_session.
From Perennial.program_proof.session Require Export versionVector sort.

Section heap.

  Context `{hG: !heapGS Σ}.
  
  Lemma wp_getGossipOperations (sv: u64*u64*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t) (s: Server.t)
    (serverId: w64) (n: nat) :
    {{{
        is_server sv s n 
    }}}
      getGossipOperations (server_val sv) #serverId
    {{{
        ns , RET slice_val (ns);
        operation_slice ns (coq_getGossipOperations s serverId) n ∗
        is_server sv s n 
    }}}.
  Proof.
    iIntros "%Φ (%H1 & %H2 & H3 & %H4 & H5 & H6 & H7 & H8 & %H9 & H10) HΦ". rewrite /getGossipOperations. wp_pures.
    wp_apply wp_NewSlice; auto. iIntros "%s1 [H1_s1 H2_s1]".
    iPoseProof (own_slice_small_sz with "[$H1_s1]") as "%H_s1_len".
    iPoseProof (own_slice_small_sz with "[$H10]") as "%YES1".
    iPoseProof (own_slice_small_sz with "[$H5]") as "%YES2".
    wp_apply wp_ref_to; auto. iIntros "%ret H_ret".
    wp_pures. wp_bind (if: #serverId ≥ slice.len sv.2 then #true else _)%E.
    wp_apply wp_slice_len; auto. wp_if_destruct.
    - wp_pures. wp_load. iModIntro. iApply "HΦ". iFrame.
      replace (replicate (uint.nat (W64 0)) operation_into_val .(IntoVal_def (Slice.t * w64))) with (@nil (Slice.t * w64)) in *; simpl in *; trivial. iSplitL "".
      + unfold coq_getGossipOperations. replace (s .(Server.GossipAcknowledgements) !! uint.nat serverId) with (@None u64).
        * iApply big_sepL2_nil. done.
        * symmetry. eapply lookup_ge_None. word.
      + iPureIntro. tauto.
    - wp_pures. wp_apply wp_slice_len; auto.
      assert (is_Some (s .(Server.GossipAcknowledgements) !! uint.nat serverId)) as [v H_v].
      { eapply lookup_lt_is_Some_2. word. }
      wp_apply (wp_SliceGet with "[$H10]"); auto.
      iIntros "H1". simpl. wp_pures. wp_if_destruct.
      + wp_load. iModIntro. iApply "HΦ". iDestruct "H7" as "[%ops [H7 H4]]".
        iPoseProof (own_slice_sz with "[$H7]") as "%YES3".
        iPoseProof (big_sepL2_length with "[$H4]") as "%YES4".
        iFrame. simpl in *. replace (replicate (uint.nat (W64 0)) (Slice.nil, W64 0)) with (@nil (Slice.t * w64)) in *; simpl in *; trivial. iSplitL "".
        * unfold coq_getGossipOperations. rewrite H_v. rewrite skipn_all2.
          { simpl. done. }
          { word. }
        * iPureIntro. tauto.
      + wp_pures. wp_apply (wp_SliceGet with "[$H1]"); auto. iIntros "H9". simpl in *.
        wp_pures. wp_apply wp_SliceSkip; auto. { word. } wp_load. iDestruct "H7" as "(%ops & [H7 H10] & H4)".
        iPoseProof (own_slice_small_sz with "[$H7]") as "%YES3".
        iPoseProof (big_sepL2_length with "[$H4]") as "%YES4".
        iPoseProof (slice_small_split with "[$H7]") as "[H7 H7']".
        { instantiate (1 := v). word. }
        wp_apply (wp_SliceAppendSlice with "[$H1_s1 $H2_s1 H7']"); auto.
        iIntros "%s2 [H1_s2 H2_s2]". replace (replicate (uint.nat (W64 0)) (Slice.nil, W64 0)) with (@nil (Slice.t * w64)) in * by reflexivity. simpl in *.
        iApply "HΦ". iPoseProof (pers_big_sepL2_is_operation with "[$H4]") as "#H10_pers". iFrame.
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
          - instantiate (1 := v). word.
          - iFrame.
        }
        iPureIntro. tauto.
  Qed.

  Lemma wp_acknowledgeGossip (sv: u64*u64*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t) (s: Server.t)
    (msgv: u64*u64*u64*u64*u64*Slice.t*u64*u64*Slice.t*u64*u64*u64*u64*u64*u64*Slice.t*u64*u64)
    (msg: Message.t) (n: nat) :
    {{{
          is_server sv s n ∗ 
          is_message msgv msg n
    }}}
      acknowledgeGossip (server_val sv) (message_val msgv)
      {{{
            r , RET r;
            is_server sv (coq_acknowledgeGossip s msg) n ∗
            is_message msgv msg n
      }}}.
  Proof.
    iIntros "%Φ (H1 & H2) H_ret".
    rewrite /acknowledgeGossip.
    iDestruct "H1" as "(%H1 & %H2 & H1 & %H3 & H4 & H5 & H6 & H7 & %H4 & H8)".
    iDestruct "H2" as "(%H5 & %H6 & %H7 & %H8 & %H9 & %H10 & H9 & %H11 & %H12 & H10 & %H13 & %H14 & %H15 & %H16 & %H17 & %H18 & %H19 & H11 & %H20 & %H21)".
    wp_pures.
    wp_apply (wp_slice_len).
    iDestruct (own_slice_small_sz with "H8") as "%H22". 
    wp_if_destruct.
    { iModIntro. iApply "H_ret". iFrame.
    assert (uint.Z msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) >=? length s.(Server.GossipAcknowledgements) = true) by word.
      iSplitL.
      - unfold coq_acknowledgeGossip.
        rewrite H. iFrame. iPureIntro.
        repeat split; auto.
      - iPureIntro. repeat split; auto.
    } 
    assert (uint.nat msgv.1.1.1.1.1.1.1.2 < length s.(Server.GossipAcknowledgements))%nat
      by word.
    apply list_lookup_lt in H as [x H].
    wp_apply (wp_SliceGet with "[H8]"). { iFrame. auto. }
    iIntros "H8".
    wp_apply (wp_maxTwoInts with "[]"). { auto. }
    iIntros (r) "%H23".
    wp_pures.
    rewrite H23.
    wp_apply (slice.wp_SliceSet with "[H8]"). { iSplitL "H8".
                                                - iApply "H8".
                                                - iPureIntro. split; auto.
                                                  unfold is_Some.
                                                  exists (u64_IntoVal.(to_val) x).
                                                  simpl. unfold list.untype.
                                                  simpl. rewrite list_lookup_fmap.
                                                  rewrite H. auto. }
    iIntros "H". wp_pures. iModIntro.
    iApply "H_ret".
    iSplitL "H H1 H4 H5 H6 H7".
    - unfold coq_acknowledgeGossip.
      assert (uint.Z msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) >=?
                           length s.(Server.GossipAcknowledgements) = false) by word.
      rewrite H0. 
      iSplit. { auto. }
      iSplit. { auto. }
      iSplitL "H1". { auto. }
      iSplit. { auto. }
      iSplitL "H4". { auto. }
      iSplitL "H5". { auto. }
      iSplitL "H6". { auto. }
      iSplitL "H7". { auto. }
      iSplit. { simpl. iPureIntro.
                rewrite length_insert. auto. }
      simpl.
      rewrite <- H14.
      rewrite H. 
      unfold own_slice_small.
      assert ((<[uint.nat msgv.1.1.1.1.1.1.1.2:=#(coq_maxTwoInts x msgv.1.1.1.1.1.2)]>
                 (list.untype s.(Server.GossipAcknowledgements))) =
              (list.untype
                 (<[uint.nat msgv.1.1.1.1.1.1.1.2:=coq_maxTwoInts x msg.(Message.S2S_Acknowledge_Gossip_Index)]>
                    s.(Server.GossipAcknowledgements)))).
      { unfold list.untype. rewrite list_fmap_insert. simpl. rewrite H16. auto. }
      rewrite H24. iFrame.
    - unfold is_message. iFrame.
      iPureIntro.
      repeat split; auto.
  Qed.

End heap.
