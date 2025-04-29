From Perennial.program_proof.session Require Export session_prelude definitions coq_session.
From Perennial.program_proof.session Require versionVector.

Definition Ev : Z := 0.
Definition Wfr : Z := 1.
Definition Mw : Z := 2.
Definition Mr : Z := 3.
Definition Ryw : Z := 4.
Definition Ca : Z := 5.

Module CoqSessionClient.

  Include Goose.github_com.session.client.

  Definition coq_read (c: Client.t) (serverId: u64) : Message.t :=
    match uint.nat c.(Client.SessionSemantic) with
    | 0%nat => Message.mk 0 (c.(Client.Id)) serverId 0 0 (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 1%nat => Message.mk 0 (c.(Client.Id)) serverId 0 0 (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 2%nat => Message.mk 0 (c.(Client.Id)) serverId 0 0 (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 3%nat => Message.mk 0 (c.(Client.Id)) serverId 0 0 (c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 4%nat => Message.mk 0 (c.(Client.Id)) serverId 0 0 (c.(Client.WriteVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 5%nat => Message.mk 0 (c.(Client.Id)) serverId 0 0 (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | _ => Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    end.

  Definition coq_write (c: Client.t) (serverId: u64) (value: u64) : Message.t :=
    match uint.nat c.(Client.SessionSemantic) with
    | 0%nat => Message.mk 0 (c.(Client.Id)) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 1%nat => Message.mk 0 (c.(Client.Id)) serverId 1 value (c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 2%nat => Message.mk 0 (c.(Client.Id)) serverId 1 value (c.(Client.WriteVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 3%nat => Message.mk 0 (c.(Client.Id)) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 4%nat => Message.mk 0 (c.(Client.Id)) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 5%nat => Message.mk 0 (c.(Client.Id)) serverId 1 value (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | _ => Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    end.

  Definition coq_processRequest (c: Client.t) (requestType: u64) (serverId: u64) (value: u64) (ackMessage: Message.t) : Client.t * Message.t :=
    match uint.nat requestType with
    | 0%nat => (c, coq_read c serverId)
    | 1%nat => (c, coq_write c serverId value)
    | 2%nat =>
      match uint.nat ackMessage.(Message.S2C_Client_OperationType) with
      | 0%nat => (Client.mk c.(Client.Id) c.(Client.NumberOfServers) c.(Client.WriteVersionVector) ackMessage.(Message.S2C_Client_VersionVector) c.(Client.SessionSemantic), Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
      | 1%nat => (Client.mk c.(Client.Id) c.(Client.NumberOfServers) (ackMessage.(Message.S2C_Client_VersionVector)) c.(Client.ReadVersionVector) c.(Client.SessionSemantic), Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
      | _ => (c, Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
      end
    | _ => (c, Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
    end.

End CoqSessionClient.

Export CoqSessionClient.

Section heap.

  Context `{hG: !heapGS Σ}.

  (*
  Lemma wp_maxTS (n: nat) (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) (dx: dfrac) (dy: dfrac) :
    {{{
        own_slice_small x uint64T dx xs ∗
        own_slice_small y uint64T dy ys ∗
        ⌜n = length xs /\ n = length ys⌝
    }}}
      CoqSessionClient.maxTS (slice_val x) (slice_val y)
    {{{
        ns, RET (slice_val ns);
        own_slice_small x uint64T dx xs ∗
        own_slice_small y uint64T dy ys ∗
        own_slice ns uint64T (DfracOwn 1) (coq_maxTS xs ys) ∗
        ⌜n = length (coq_maxTS xs ys)⌝
    }}}.
  Proof.
    replace (maxTS x y) with (CoqSessionServer.maxTS (slice_val x) (slice_val y)) by reflexivity.
    iIntros "%Φ (H_xs & H_ys & [%LEN_xs %LEN_ys]) HΦ".
    wp_apply (versionVector.wp_maxTS with "[$H_xs $H_ys]"). { iPureIntro. word. }
    iIntros "%ns (H_ns & H_xs & H_ys)". iApply "HΦ". iFrame.
    iPureIntro. revert n xs ys LEN_xs LEN_ys; clear.
    induction n as [ | n IH], xs as [ | x xs], ys as [ | y ys]; simpl; intros; try congruence.
    f_equal; eapply IH; word.
  Qed.

  Lemma wp_read (c: Client.t) (serverId: u64) (n: nat) cv :
    {{{
        is_client cv c n ∗
        ⌜CLIENT_INVARIANT c⌝
    }}}
      CoqSessionClient.read (client_val cv) (#serverId)
    {{{
        msgv, RET (message_val msgv);
        is_client cv c n ∗
        is_message msgv (coq_read c serverId) n n 0%nat
    }}}.
  Proof.
    rewrite redefine_client_val redefine_message_val. TypeVector.des cv. iIntros "%Φ (H_is_client & %H_invariant) HΦ".
    iDestruct "H_is_client" as "(%H1 & %H2 & -> & H3 & %H4 & H5 & %H6 & %H7)". destruct H_invariant as [? ?].
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
      - unfold coq_read. rewrite -> EQ. replace (uint.nat (W64 0)) with 0%nat by word.
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
      - unfold coq_read. rewrite -> EQ. replace (uint.nat (W64 1)) with 1%nat by word.
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
      - unfold coq_read. rewrite -> EQ. replace (uint.nat (W64 2)) with 2%nat by word.
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
    { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil w64) by reflexivity.
      wp_pures. wp_apply (wp_SliceAppendSlice with "[H5 H_s1]"). { repeat econstructor; eauto. } { iFrame. } clear s1. iIntros "%s1 [H_s1 H5]".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_load.
      apply bool_decide_eq_true in Heqb2.
      assert (c .(Client.SessionSemantic) = W64 3) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_read. rewrite -> EQ. replace (uint.nat (W64 3)) with 3%nat by word.
        unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
        iSplitL "". { done. }
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
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 4))) as [ | ] eqn: Heqb3.
    { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil w64) by reflexivity.
      wp_pures. wp_apply (wp_SliceAppendSlice with "[H3 H_s1]"). { repeat econstructor; eauto. } { iFrame. } clear s1. iIntros "%s1 [H_s1 H3]".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_load.
      apply bool_decide_eq_true in Heqb3.
      assert (c .(Client.SessionSemantic) = W64 4) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_read. rewrite -> EQ. replace (uint.nat (W64 4)) with 4%nat by word.
        unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
        iSplitL "". { done. }
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
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 5))) as [ | ] eqn: Heqb4.
    { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_maxTS (uint.nat (c.(Client.NumberOfServers))) with "[$H3 $H5]"). { iPureIntro. word. } iIntros "%s1 (H3 & H5 & [H_s1 %LEN])".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_load.
      apply bool_decide_eq_true in Heqb4.
      assert (c .(Client.SessionSemantic) = W64 5) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_read. rewrite -> EQ. replace (uint.nat (W64 5)) with 5%nat by word.
        unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
        iSplitL "". { done. }
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
    { wp_pures. wp_load. replace (Φ (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0))) by reflexivity.
      iModIntro. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - rewrite -> bool_decide_eq_false in Heqb, Heqb0, Heqb1, Heqb2, Heqb3, Heqb4.
        assert (c.(Client.SessionSemantic) ≠ (W64 0)) as NE0 by congruence.
        assert (c.(Client.SessionSemantic) ≠ (W64 1)) as NE1 by congruence.
        assert (c.(Client.SessionSemantic) ≠ (W64 2)) as NE2 by congruence.
        assert (c.(Client.SessionSemantic) ≠ (W64 3)) as NE3 by congruence.
        assert (c.(Client.SessionSemantic) ≠ (W64 4)) as NE4 by congruence.
        assert (c.(Client.SessionSemantic) ≠ (W64 5)) as NE5 by congruence.
        unfold coq_read. destruct (uint.nat c .(Client.SessionSemantic)) as [ | [ | [ | [ | [ | [ | n]]]]]] eqn: H_n; try word.
    }
  Qed.

  Lemma wp_write (c: Client.t) (serverId: u64) (value: u64) (n: nat) cv :
    {{{
        is_client cv c n ∗
        ⌜CLIENT_INVARIANT c⌝
    }}}
      CoqSessionClient.write (client_val cv) (#serverId) (#value)
    {{{
        msgv, RET (message_val msgv);
        is_client cv c n ∗
        is_message msgv (coq_write c serverId value) n n 0%nat
    }}}.
  Proof.
    rewrite redefine_client_val redefine_message_val. TypeVector.des cv. iIntros "%Φ (H_is_client & %H_invariant) HΦ".
    iDestruct "H_is_client" as "(%H1 & %H2 & -> & H3 & %H4 & H5 & %H6 & %H7)". destruct H_invariant as [? ?].
    simplNotation; simpl; subst; rewrite /CoqSessionClient.write.
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
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 1), (#value, (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 1, value, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_write. rewrite -> EQ. replace (uint.nat (W64 0)) with 0%nat by word.
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
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 3))) as [ | ] eqn: Heqb0.
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
      assert (c .(Client.SessionSemantic) = W64 3) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 1), (#value, (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 1, value, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_write. rewrite -> EQ. replace (uint.nat (W64 3)) with 3%nat by word.
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
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 4))) as [ | ] eqn: Heqb1.
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
      assert (c .(Client.SessionSemantic) = W64 4) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 1), (#value, (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 1, value, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_write. rewrite -> EQ. replace (uint.nat (W64 4)) with 4%nat by word.
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
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 1))) as [ | ] eqn: Heqb2.
    { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
      wp_pures. wp_apply (wp_SliceAppendSlice with "[H5 H_s1]"). { repeat econstructor; eauto. } { iFrame. } clear s1. iIntros "%s1 [H_s1 H5]".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_load.
      apply bool_decide_eq_true in Heqb2.
      assert (c .(Client.SessionSemantic) = W64 1) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 1), (#value, (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 1, value, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_write. rewrite -> EQ. replace (uint.nat (W64 1)) with 1%nat by word.
        unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
        iSplitL "". { iPureIntro. word. }
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
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 2))) as [ | ] eqn: Heqb3.
    { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
      wp_pures. wp_apply (wp_SliceAppendSlice with "[H3 H_s1]"). { repeat econstructor; eauto. } { iFrame. } clear s1. iIntros "%s1 [H_s1 H3]".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_load.
      apply bool_decide_eq_true in Heqb3.
      assert (c .(Client.SessionSemantic) = W64 2) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 1), (#value, (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 1, value, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_write. rewrite -> EQ. replace (uint.nat (W64 2)) with 2%nat by word.
        unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
        iSplitL "". { iPureIntro. word. }
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
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 5))) as [ | ] eqn: Heqb4.
    { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_maxTS (uint.nat (c.(Client.NumberOfServers))) with "[$H3 $H5]"). { iPureIntro. word. } iIntros "%s1 (H3 & H5 & [H_s1 %LEN])".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_load.
      apply bool_decide_eq_true in Heqb4.
      assert (c .(Client.SessionSemantic) = W64 5) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 1), (#value, (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 1, value, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_write. rewrite -> EQ. replace (uint.nat (W64 5)) with 5%nat by word.
        unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
        iSplitL "". { iPureIntro. word. }
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
    { wp_pures. wp_load. replace (Φ (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0))) by reflexivity.
      iModIntro. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - rewrite -> bool_decide_eq_false in Heqb, Heqb0, Heqb1, Heqb2, Heqb3, Heqb4.
        assert (c.(Client.SessionSemantic) ≠ (W64 0)) as NE0 by congruence.
        assert (c.(Client.SessionSemantic) ≠ (W64 1)) as NE1 by congruence.
        assert (c.(Client.SessionSemantic) ≠ (W64 2)) as NE2 by congruence.
        assert (c.(Client.SessionSemantic) ≠ (W64 3)) as NE3 by congruence.
        assert (c.(Client.SessionSemantic) ≠ (W64 4)) as NE4 by congruence.
        assert (c.(Client.SessionSemantic) ≠ (W64 5)) as NE5 by congruence.
        unfold coq_read. destruct (uint.nat c .(Client.SessionSemantic)) as [ | [ | [ | [ | [ | [ | n]]]]]] eqn: H_n; try word.
    }
  Qed.

  Lemma wp_processRequest (c: Client.t) (requestType: u64) (serverId: u64) (value: u64) (ackMessage: Message.t) (n: nat) cv msgv :
    {{{
        is_client cv c n ∗
        is_message msgv ackMessage n n n ∗
        ⌜CLIENT_INVARIANT c⌝
    }}}
      CoqSessionClient.processRequest (client_val cv) (#requestType) (#serverId) (#value) (message_val msgv)
    {{{
        cv' msgv', RET (client_val cv', message_val msgv');
        is_client cv' (coq_processRequest c requestType serverId value ackMessage).1 n ∗
        is_message msgv' (coq_processRequest c requestType serverId value ackMessage).2 n (if (uint.Z requestType =? 0)%Z || (uint.Z requestType =? 1)%Z then n else 0%nat) 0%nat ∗
        is_message msgv ackMessage n n n ∗
        ⌜CLIENT_INVARIANT (coq_processRequest c requestType serverId value ackMessage).1⌝
    }}}.
  Proof.
    TypeVector.des cv. TypeVector.des msgv. iIntros "%Φ (H_is_client & H_is_message & %H_invariant) HΦ".
    iDestruct "H_is_client" as "(%H1 & %H2 & -> & H3 & %H4 & H5 & %H6 & %H7)". iDestruct "H_is_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & %H19 & H20 & %H21 & %H22 & %H23 & %H24 & %H25 & %H26 & H27 & %H28 & %H29 & %H30)".
    simplNotation; simpl; subst; rewrite /CoqSessionClient.processRequest.
    iPoseProof (own_slice_small_sz with "[$H3]") as "%LENGTH1".
    iPoseProof (own_slice_small_sz with "[$H5]") as "%LENGTH2".
    wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%nc H_nc".
    wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%msg H_msg".
    wp_pures. wp_if_destruct.
    { wp_apply (wp_read c serverId (uint.nat c.(Client.NumberOfServers)) with "[H3 H5]"). { iFrame. simplNotation; simpl; iPureIntro. tauto. } iIntros "%msgv [H_is_client H_msgv]".
      replace (message_val msgv) with (message_into_val.(to_val) msgv) by reflexivity.
      wp_pures; eapply (tac_wp_store_ty _ _ _ _ _ _ []%list); [repeat econstructor; eauto | tc_solve | let l := msg in iAssumptionCore | reflexivity | simpl].
      wp_pures. wp_load.
      wp_pures. wp_load.
      replace (#c .(Client.Id), (#c .(Client.NumberOfServers), (t0, (t, (#c .(Client.SessionSemantic), #())))))%V with (client_val (c.(Client.Id), c.(Client.NumberOfServers), t0, t, c.(Client.SessionSemantic))) by reflexivity.
      wp_pures. iModIntro. iApply "HΦ".
      replace (uint.Z (W64 0) =? 0)%Z with true by reflexivity. rewrite orb_true_l.
      iFrame; simplNotation; simpl. iPureIntro; tauto.
    }
    wp_pures. wp_if_destruct.
    { wp_apply (wp_write c serverId value (uint.nat c.(Client.NumberOfServers)) with "[H3 H5]"). { iFrame. simplNotation; simpl; iPureIntro. tauto. } iIntros "%msgv [H_is_client H_msgv]".
      replace (message_val msgv) with (message_into_val.(to_val) msgv) by reflexivity.
      wp_pures; eapply (tac_wp_store_ty _ _ _ _ _ _ []%list); [repeat econstructor; eauto | tc_solve | let l := msg in iAssumptionCore | reflexivity | simpl].
      wp_pures. wp_load.
      wp_pures. wp_load.
      replace (#c .(Client.Id), (#c .(Client.NumberOfServers), (t0, (t, (#c .(Client.SessionSemantic), #())))))%V with (client_val (c.(Client.Id), c.(Client.NumberOfServers), t0, t, c.(Client.SessionSemantic))) by reflexivity.
      wp_pures. iModIntro. iApply "HΦ".
      replace (uint.Z (W64 1) =? 1)%Z with true by reflexivity. rewrite orb_true_r.
      iFrame; simplNotation; simpl. iPureIntro; tauto.
    }
    wp_pures. wp_if_destruct.
    { wp_pures. wp_if_destruct.
      { wp_apply wp_NewSlice. iIntros "%s1 H_s1". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil w64) by reflexivity.
        wp_pures. wp_apply (wp_SliceAppendSlice with "[H_s1 H27]"). { repeat econstructor; eauto. } { iFrame. } simpl. clear s1. iIntros "%s1 [H_s1 H27]".
        wp_pures. wp_apply (wp_storeField_struct with "[H_nc]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_nc".
        wp_pures. rewrite Heqb1. wp_pures.
        wp_pures. wp_load.
        wp_pures. wp_load.
        replace (#c .(Client.Id), (#c .(Client.NumberOfServers), (t0, (s1, (#c .(Client.SessionSemantic), #())))))%V with (client_val (c.(Client.Id), c.(Client.NumberOfServers), t0, s1, c.(Client.SessionSemantic))) by reflexivity.
        replace (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V with (message_val (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)) by reflexivity.
        wp_pures. iModIntro. iApply "HΦ".
        replace ((uint.Z (W64 2) =? 0) || (uint.Z (W64 2) =? 1)) with false by reflexivity.
        unfold coq_processRequest.
        replace (uint.nat (W64 2)) with 2%nat by reflexivity.
        replace (uint.nat ackMessage .(Message.S2C_Client_OperationType)) with 0%nat by word.
        simpl.
        iPoseProof (own_slice_to_small with "[$H_s1]") as "H_s1".
        iFrame; simplNotation; simpl.
        iSplitL "". { iPureIntro; tauto. }
        iSplitR "".
        { unfold is_message; iFrame; simplNotation; simpl.
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { iApply (own_slice_small_nil); eauto. }
          iSplitL "". { iPureIntro. word. }
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
        iSplitL "". { iPureIntro; repeat (split; trivial). word. }
        iPureIntro. destruct H_invariant as [? ?]; split; trivial.
      }
      wp_pures. wp_if_destruct.
      { wp_apply wp_NewSlice. iIntros "%s1 H_s1". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with ( @nil w64) by reflexivity.
        wp_pures. wp_apply (wp_SliceAppendSlice with "[H_s1 H27]"). { repeat econstructor; eauto. } { iFrame. } simpl. clear s1. iIntros "%s1 [H_s1 H27]".
        wp_pures. wp_apply (wp_storeField_struct with "[H_nc]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_nc".
        wp_pures. wp_load.
        wp_pures. wp_load.
        replace (#c .(Client.Id), (#c .(Client.NumberOfServers), (s1, (t, (#c .(Client.SessionSemantic), #())))))%V with (client_val (c.(Client.Id), c.(Client.NumberOfServers), s1, t, c.(Client.SessionSemantic))) by reflexivity.
        replace (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V with (message_val (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)) by reflexivity.
        wp_pures. iModIntro. iApply "HΦ".
        replace ((uint.Z (W64 2) =? 0) || (uint.Z (W64 2) =? 1)) with false by reflexivity.
        unfold coq_processRequest.
        replace (uint.nat (W64 2)) with 2%nat by reflexivity.
        replace (uint.nat ackMessage .(Message.S2C_Client_OperationType)) with 1%nat by word.
        simpl.
        iPoseProof (own_slice_to_small with "[$H_s1]") as "H_s1".
        iFrame; simplNotation; simpl.
        iSplitL "". { iPureIntro; tauto. }
        iSplitR "".
        { unfold is_message; iFrame; simplNotation; simpl.
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { iApply (own_slice_small_nil); eauto. }
          iSplitL "". { iPureIntro. word. }
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
        iSplitL "". { iPureIntro; repeat (split; trivial). }
        iPureIntro. destruct H_invariant as [? ?]; split; trivial.
      }
      { wp_pures. wp_load.
        wp_pures. wp_load.
        wp_pures.
        replace (#c .(Client.Id), (#c .(Client.NumberOfServers), (t0, (t, (#c .(Client.SessionSemantic), #())))))%V with (client_val (c.(Client.Id), c.(Client.NumberOfServers), t0, t, c.(Client.SessionSemantic))) by reflexivity.
        replace (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V with (message_val (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)) by reflexivity.
        iModIntro. iApply "HΦ".
        replace (uint.Z (W64 2) =? 0)%Z with false by reflexivity. replace (uint.Z (W64 2) =? 1)%Z with false by reflexivity. simpl.
        unfold coq_processRequest. replace (uint.nat (W64 2)) with 2%nat by word.
        destruct (uint.nat ackMessage .(Message.S2C_Client_OperationType)) as [ | [ | n]] eqn: H_OBS; try word.
        iFrame. simplNotation; simpl.
        iSplitL "". { iPureIntro. tauto. }
        iSplitR "".
        { unfold is_message; iFrame; simplNotation; simpl.
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { done. }
          iSplitL "". { iApply (own_slice_small_nil); eauto. }
          iSplitL "". { done. }
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
        iPureIntro; tauto.
      }
    }
    { wp_pures. wp_load.
      wp_pures. wp_load.
      wp_pures.
      replace (#c .(Client.Id), (#c .(Client.NumberOfServers), (t0, (t, (#c .(Client.SessionSemantic), #())))))%V with (client_val (c.(Client.Id), c.(Client.NumberOfServers), t0, t, c.(Client.SessionSemantic))) by reflexivity.
      replace (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V with (message_val (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)) by reflexivity.
      iModIntro. iApply "HΦ".
      replace (uint.Z (W64 2) =? 0)%Z with false by reflexivity. replace (uint.Z (W64 2) =? 1)%Z with false by reflexivity. simpl.
      unfold coq_processRequest. destruct (uint.nat requestType) as [ | [ | [ | n]]] eqn: H_OBS; try word; simpl.
      replace (uint.Z requestType =? 0)%Z with false by word. replace (uint.Z requestType =? 1)%Z with false by word. simpl.
      iFrame. simplNotation; simpl.
      iSplitL "". { iPureIntro. tauto. }
      iSplitR "".
      { unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply (own_slice_small_nil); eauto. }
        iSplitL "". { done. }
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
      iPureIntro; tauto.
    }
  Qed.
  *)

End heap.
