From Perennial.program_proof.session Require Export session_prelude.
From Perennial.program_proof.session Require Export definitions.

Definition getOperationVersionVector (op: Operation.t) : list u64 :=
  op.(Operation.VersionVector).

Lemma OperationVersionVector_dec (v1: list u64) (v2: list u64)
  : {v1 = v2} + {v1 ≠ v2}.
Proof.
  pose proof (w64_eq_dec) as H; do 2 red in H. decide equality.
Qed.

Lemma Operation_dec (op1: Operation.t) (op2: Operation.t)
  : {op1 = op2} + {op1 ≠ op2}.
Proof.
  pose proof (w64_eq_dec) as H; do 2 red in H. pose proof (OperationVersionVector_dec) as H'. decide equality.
Qed.


Module CoqSessionServer.

  Include Goose.github_com.session.server.

  Fixpoint coq_compareVersionVector (v1: list u64) (v2: list u64) : bool :=
    match v1 with
    | [] => true
    | h1 :: t1 =>
      match v2 with
      | [] => true
      | h2 :: t2 => if uint.Z h1 <? uint.Z h2 then false else coq_compareVersionVector t1 t2
      end
    end.

  Fixpoint coq_lexicographicCompare (v1: list u64) (v2: list u64) : bool :=
    match v1 with
    | [] => false 
    | h1 :: t1 =>
      match v2 with
      | [] => false 
      | h2 :: t2 => if uint.Z h1 =? uint.Z h2 then coq_lexicographicCompare t1 t2 else uint.Z h1 >? uint.Z h2
      end
    end.

  Definition coq_maxTwoInts (x: u64) (y: u64) : u64 :=
    if uint.Z x >? uint.Z y then x else y. 

  Fixpoint coq_maxTS (t1: list u64) (t2: list u64) : list u64 :=
    match t1 with
    | [] => []
    | hd1 :: tl1 =>
      match t2 with
      | [] => [] 
      | hd2 :: tl2 => coq_maxTwoInts hd1 hd2 :: coq_maxTS tl1 tl2
      end
    end.

  Definition coq_oneOffVersionVector (v1: list u64) (v2: list u64) : bool :=
    let loop_step (acc: bool * bool) (element: u64 * u64) : bool * bool :=
      let (e1, e2) := element in
      let (output, canApply) := acc in
      if canApply && (uint.Z (w64_word_instance.(word.add) e1 (W64 1)) =? uint.Z e2) then
        (output, false)
      else if uint.Z e1 >=? uint.Z e2 then
        (output, canApply)
      else 
        (false, canApply)
    in
    let (output, canApply) := fold_left loop_step (zip v1 v2) (true, true) in
    output && negb canApply.

  Fixpoint coq_equalSlices (s1: list u64) (s2: list u64) : bool :=
    match s1 with
    | [] => true
    | h1 :: t1 =>
      match s2 with
      | [] => true
      | h2 :: t2 => if negb (uint.Z h1 =? uint.Z h2) then false else coq_equalSlices t1 t2
      end
    end.

  Definition coq_equalOperations (o1: Operation.t) (o2: Operation.t) : bool :=
    coq_equalSlices o1.(Operation.VersionVector) o2.(Operation.VersionVector) && (uint.Z o1.(Operation.Data) =? uint.Z (o2.(Operation.Data))).

  Variant binarySearch_spec (needle: Operation.t) (l: list Operation.t) (n: nat) (RESULT: nat) : Prop :=
    | binarySearch_spec_intro prefix suffix
      (LENGTH: RESULT = length prefix)
      (VECTOR: map getOperationVersionVector l = if forallb (fun x => negb (coq_equalSlices x.(Operation.VersionVector) needle.(Operation.VersionVector))) l then prefix ++ suffix else prefix ++ [getOperationVersionVector needle] ++ suffix)
      (PREFIX: ∀ op, In op prefix -> coq_lexicographicCompare needle.(Operation.VersionVector) op = true)
      (SUFFIX: ∀ op, In op suffix -> coq_lexicographicCompare op needle.(Operation.VersionVector) = true)
      : binarySearch_spec needle l n RESULT.

  Fixpoint coq_sortedInsert (l: list Operation.t) (i: Operation.t) : list Operation.t :=
    match l with
    | [] => [i]
    | h :: t =>
      if coq_lexicographicCompare h.(Operation.VersionVector) i.(Operation.VersionVector) then
        i :: h :: t
      else if coq_equalSlices h.(Operation.VersionVector) i.(Operation.VersionVector) then
        h :: t
      else
        h :: coq_sortedInsert t i
    end.

  Definition coq_deleteAtIndexOperation (o: list Operation.t) (index: nat) : list Operation.t :=
    take index o ++ drop (index + 1)%nat o.

  Definition coq_deleteAtIndexMessage (m: list Message.t) (index: nat) : list Message.t :=
    take index m ++ drop (index + 1)%nat m.

  Definition coq_getDataFromOperationLog (l: list Operation.t) : u64 :=
    match last l with
    | Some v => v.(Operation.Data)
    | None => W64 0
    end.

  Definition coq_receiveGossip (server: Server.t) (request: Message.t) : Server.t :=
    if (length request.(Message.S2S_Gossip_Operations) =? 0)%nat then
      server
    else
      let first_loop_output : Server.t :=
        let focus := request.(Message.S2S_Gossip_Operations) in
        let loop_step (acc: Server.t) (elem: Operation.t) : Server.t :=
          let server := acc in
          if coq_oneOffVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector) then
            {|
              Server.Id := server.(Server.Id);
              Server.NumberOfServers := server.(Server.NumberOfServers);
              Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests);
              Server.VectorClock := coq_maxTS server.(Server.VectorClock) elem.(Operation.VersionVector);
              Server.OperationsPerformed := coq_sortedInsert server.(Server.OperationsPerformed) elem;
              Server.MyOperations := server.(Server.MyOperations);
              Server.PendingOperations := server.(Server.PendingOperations);
              Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements);
            |}
          else if negb (coq_compareVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector)) then
            {|
              Server.Id := server.(Server.Id);
              Server.NumberOfServers := server.(Server.NumberOfServers);
              Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests);
              Server.VectorClock := server.(Server.VectorClock);
              Server.OperationsPerformed := server.(Server.OperationsPerformed);
              Server.MyOperations := server.(Server.MyOperations);
              Server.PendingOperations := coq_sortedInsert server.(Server.PendingOperations) elem;
              Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements);
            |}
          else
            server
        in
        fold_left loop_step focus server
      in
      let server := first_loop_output in
      let second_loop_output : Server.t * nat * list u64 :=
        let focus := server.(Server.PendingOperations) in
        let loop_step (acc: Server.t * nat * list u64) (elem: Operation.t) : Server.t * nat * list u64 :=
          let '(server, i, seen) := acc in
            if coq_oneOffVersionVector server.(Server.VectorClock) elem.(Operation.VersionVector) then
              (Server.mk server.(Server.Id) server.(Server.NumberOfServers) server.(Server.UnsatisfiedRequests) (coq_maxTS server.(Server.VectorClock) elem.(Operation.VersionVector)) (coq_sortedInsert server.(Server.OperationsPerformed) elem) server.(Server.MyOperations) server.(Server.PendingOperations) server.(Server.GossipAcknowledgements), (i + 1)%nat, seen ++ [W64 (Z.of_nat i)])
            else
              (server, (i + 1)%nat, seen)
        in
        fold_left loop_step focus (server, 0%nat, [])
      in
      let '(server, _, seen) := second_loop_output in
      let third_loop_output : nat * nat * list Operation.t :=
        let focus := server.(Server.PendingOperations) in
        let loop_step (acc: nat * nat * list Operation.t) (elem: Operation.t) : nat * nat * list Operation.t :=
          let '(i, j, output) := acc in
          match seen !! j with
          | Some i' => if (i =? uint.nat i')%nat then ((i + 1)%nat, (j + 1)%nat, output) else ((i + 1)%nat, j, output ++ [elem])
          | None => ((i + 1)%nat, j, output ++ [elem])
          end
        in
        fold_left loop_step focus (0%nat, 0%nat, [])
      in
      let '(_, _, output) := third_loop_output in
      {|
        Server.Id := server.(Server.Id);
        Server.NumberOfServers := server.(Server.NumberOfServers);
        Server.UnsatisfiedRequests := server.(Server.UnsatisfiedRequests);
        Server.VectorClock := server.(Server.VectorClock);
        Server.OperationsPerformed := server.(Server.OperationsPerformed);
        Server.MyOperations := server.(Server.MyOperations);
        Server.PendingOperations := output;
        Server.GossipAcknowledgements := server.(Server.GossipAcknowledgements);
      |}.

  Definition coq_acknowledgeGossip (s: Server.t) (r: Message.t) : Server.t :=
    let i := uint.nat (r.(Message.S2S_Acknowledge_Gossip_Sending_ServerId)) in
    let l := s.(Server.GossipAcknowledgements) in
    if (i >=? length l)%nat then
      s
    else
      let prevGossipAcknowledgementsValue : u64 :=
        match s.(Server.GossipAcknowledgements) !! i with
        | Some x => x
        | None => W64 0
        end
      in
      let newGossipAcknowledgements := coq_maxTwoInts prevGossipAcknowledgementsValue r.(Message.S2S_Acknowledge_Gossip_Index) in
      let gossipAcknowledgements := <[i := newGossipAcknowledgements]> l in
      Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) gossipAcknowledgements.

  Definition coq_getGossipOperations (s: Server.t) (serverId: u64) : list Operation.t :=
    match s.(Server.GossipAcknowledgements) !! uint.nat serverId with
    | Some v => drop (uint.nat v) s.(Server.MyOperations)
    | None => []
    end.

  Definition coq_processClientRequest (s: Server.t) (r: Message.t) : bool * Server.t * Message.t :=
    if negb (coq_compareVersionVector s.(Server.VectorClock) r.(Message.C2S_Client_VersionVector)) then
      (false, s, Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
    else
      if uint.Z r.(Message.C2S_Client_OperationType) =? 0 then
        let S2C_Client_Data := coq_getDataFromOperationLog s.(Server.OperationsPerformed) in
        let S2C_Client_VersionVector := s.(Server.VectorClock) in
        let S2C_Client_Number := r.(Message.C2S_Client_Id) in
        let S2C_Server_Id := s.(Server.Id) in
        (true, s, Message.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 0 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number)
      else
        let v := match s.(Server.VectorClock) !! uint.nat s.(Server.Id) with Some v => uint.Z v | None => 0 end in
        if (v <=? CONSTANT - 1)%Z && (length s.(Server.MyOperations) <=? CONSTANT - 1)%Z then
          let VectorClock := <[uint.nat s.(Server.Id) := W64 (v + 1)]> s.(Server.VectorClock) in
          let OperationsPerformed := coq_sortedInsert s.(Server.OperationsPerformed) (Operation.mk VectorClock r.(Message.C2S_Client_Data)) in
          let MyOperations := coq_sortedInsert s.(Server.MyOperations) (Operation.mk VectorClock r.(Message.C2S_Client_Data)) in
          let S2C_Client_OperationType := 1 in
          let S2C_Client_Data := 0 in
          let S2C_Client_VersionVector := VectorClock in
          let S2C_Client_Number := r.(Message.C2S_Client_Id) in
          let S2C_Server_Id := s.(Server.Id) in
          (true, Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed MyOperations s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), Message.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 1 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number)
        else
          (false, s, Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0).

  Definition coq_processRequest (server: Server.t) (request: Message.t) : Server.t * list Message.t :=
    match uint.nat request.(Message.MessageType) with
    | 0%nat =>
      let '(succeeded, server, reply) := coq_processClientRequest server request in
      if succeeded then
        (server, [reply])
      else
        let UnsatisfiedRequests := server.(Server.UnsatisfiedRequests) ++ [request] in 
        let server := Server.mk server.(Server.Id) server.(Server.NumberOfServers) UnsatisfiedRequests server.(Server.VectorClock) server.(Server.OperationsPerformed) server.(Server.MyOperations) server.(Server.PendingOperations) server.(Server.GossipAcknowledgements) in
        (server, [])
    | 1%nat =>
      let server := coq_receiveGossip server request in
      let focus := server.(Server.UnsatisfiedRequests) in
      let loop_init : nat * Server.t * list Message.t :=
        (0%nat, server, [])
      in
      let loop_step (acc: nat * Server.t * list Message.t) (element: Message.t) : nat * Server.t * list Message.t :=
        let '(i, s, outGoingRequests) := acc in
        let '(succeeded, s, reply) := coq_processClientRequest s element in
        if succeeded then
          let UnsatisfiedRequests := coq_deleteAtIndexMessage s.(Server.UnsatisfiedRequests) i in
          (i, Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), outGoingRequests ++ [reply])
        else
          ((i + 1)%nat, s, outGoingRequests)
      in
      let '(_, server, outGoingRequests) := fold_left loop_step focus loop_init in
      (server, outGoingRequests)
    | 2%nat => (coq_acknowledgeGossip server request, [])
    | 3%nat =>
      let loop_step (acc: Server.t * list Message.t) (index: u64) : Server.t * list Message.t :=
        let '(server, outGoingRequests) := acc in
        if negb (uint.nat index =? uint.nat server.(Server.Id))%nat && negb (length (coq_getGossipOperations server index) =? 0)%nat then
          let GossipAcknowledgements := <[uint.nat index := W64 (length server.(Server.MyOperations))]> server.(Server.GossipAcknowledgements) in
          let S2S_Gossip_Sending_ServerId := server.(Server.Id) in
          let S2S_Gossip_Receiving_ServerId := index in
          let S2S_Gossip_Operations := coq_getGossipOperations server index in
          let S2S_Gossip_Index := length (server.(Server.MyOperations)) in
          let message := Message.mk 1 0 0 0 0 [] S2S_Gossip_Sending_ServerId S2S_Gossip_Receiving_ServerId S2S_Gossip_Operations S2S_Gossip_Index 0 0 0 0 0 [] 0 0 in
          (Server.mk server.(Server.Id) server.(Server.NumberOfServers) server.(Server.UnsatisfiedRequests) server.(Server.VectorClock) server.(Server.OperationsPerformed) server.(Server.MyOperations) server.(Server.PendingOperations) GossipAcknowledgements, outGoingRequests ++ [message])
        else
          (server, outGoingRequests)
      in
      let nat_to_u64 (i: nat) : u64 :=
        W64 i
      in
      let focus := map nat_to_u64 (seq 0%nat (uint.nat server.(Server.NumberOfServers))) in
      fold_left loop_step focus (server, [])
    | _ => (server, [])
    end.

End CoqSessionServer.

Export CoqSessionServer.

Section properties.

  Import SessionPrelude.

  Lemma Forall_CONSTANT_replicate n
    : Forall u64_le_CONSTANT (replicate n (W64 0)).
  Proof.
    induction n as [ | n IH]; simpl; econstructor; eauto. eapply CONSTANT_ge_0.
  Qed.

  Lemma CONSTANT_coq_maxTs xs ys
    (H_xs : Forall u64_le_CONSTANT xs)
    (H_ys : Forall u64_le_CONSTANT ys)
    : Forall u64_le_CONSTANT (coq_maxTS xs ys).
  Proof.
    revert ys H_ys; induction H_xs as [ | x xs H_x H_xs IH]; intros ys H_ys; destruct H_ys as [ | y ys H_y H_ys]; simpl in *; try congruence; econstructor; simpl; eauto.
    unfold coq_maxTwoInts. red in H_x, H_y |- *. rewrite -> CONSTANT_unfold in *. rewrite Z.gtb_ltb. destruct (_ <? _) as [ | ] eqn: H_OBS; [rewrite Z.ltb_lt in H_OBS | rewrite Z.ltb_nlt in H_OBS]; word.
  Qed.

  Lemma redefine_coq_lexicographicCompare :
    coq_lexicographicCompare = vectorGt.
  Proof.
    reflexivity.
  Defined.

  Lemma redefine_coq_equalSlices :
    coq_equalSlices = vectorEq.
  Proof.
    reflexivity.
  Defined.

  Definition Operation_wf (len : nat) (o : Operation.t) : Prop :=
    Forall (fun _ => True) o.(Operation.VersionVector) /\ length o.(Operation.VersionVector) = len.

  #[global]
  Instance hsEq_Operation (len : nat) : hsEq Operation.t (well_formed := Operation_wf len) :=
    hsEq_preimage getOperationVersionVector.

  #[global]
  Instance hsOrd_Operation (len : nat) : hsOrd Operation.t (hsEq := hsEq_Operation len) :=
    hsOrd_preimage getOperationVersionVector.

  Lemma redefine_coq_sortedInsert (len : nat) :
    coq_sortedInsert = sortedInsert (hsOrd := hsOrd_Operation len).
  Proof.
    reflexivity.
  Defined.

  #[local] Hint Resolve @Forall_True : core.

  Lemma aux0_equalSlices l1 l2 :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = true ->
    l1 = l2.
  Proof.
    rewrite redefine_coq_equalSlices. intros. rewrite <- vectorEq_true_iff; eauto 2.
  Qed.

  Lemma aux1_equalSlices l1 l2 :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = false ->
    l1 ≠ l2.
  Proof.
    rewrite redefine_coq_equalSlices. intros. rewrite <- vectorEq_true_iff; eauto 2.
    rewrite H0; congruence.
  Qed.

  Lemma aux2_equalSlices l1 l2 b :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = b ->
    coq_equalSlices l2 l1 = b.
  Proof.
    rewrite redefine_coq_equalSlices. intros. subst b. eapply (eqb_comm (hsEq_A := hsEq_vector (length l1))); eauto.
  Qed.

  Lemma aux3_equalSlices l :
    coq_equalSlices l l = true.
  Proof.
    change (coq_equalSlices l l) with (eqb (hsEq := hsEq_vector (length l)) l l).
    rewrite eqb_eq; eauto 2. eapply eqProp_reflexivity; eauto 2.
  Qed.

  Lemma aux0_lexicographicCompare l1 l2 l3 :
    coq_lexicographicCompare l2 l1 = true ->
    coq_lexicographicCompare l3 l2 = true ->
    coq_lexicographicCompare l3 l1 = true.
  Proof.
    rewrite redefine_coq_lexicographicCompare.
    intros. eapply vectorGt_transitive; eauto.
  Qed.

  Lemma aux1_lexicographicCompare l1 l2 :
    length l1 = length l2 -> 
    l1 ≠ l2 ->
    (coq_lexicographicCompare l2 l1 = false <-> coq_lexicographicCompare l1 l2 = true).
  Proof.
    rewrite redefine_coq_lexicographicCompare. remember (length l1) as len eqn: len_eq.
    pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector len) l1 l2) as claim. simpl in claim.
    symmetry in len_eq. intros len_eq'. symmetry in len_eq'.
    specialize (claim (conj (Forall_True _) len_eq) (conj (Forall_True _) len_eq')).
    destruct claim as [H_lt | [H_eq | H_gt]].
    - rewrite H_lt. intros NE. split.
      { congruence. }
      intros l1_gt_l2. contradiction (ltProp_irreflexivity (hsOrd := hsOrd_vector len) l1 l1); eauto.
      + eapply eqProp_reflexivity; eauto.
      + eapply ltProp_transitivity with (y := l2); eauto.
    - intros NE. contradiction NE. clear NE. rewrite <- vectorEq_true_iff; eauto 2.
      change (eqb (hsEq := hsEq_vector len) l1 l2 = true). rewrite eqb_eq; eauto 2.
    - rewrite H_gt. intros NE. split.
      { congruence. }
      intros _. change (ltb (hsOrd := hsOrd_vector len) l1 l2 = false).
      rewrite ltb_nlt; eauto 2. intros NLT. change (ltb (hsOrd := hsOrd_vector len) l2 l1 = true) in H_gt.
      rewrite ltb_lt in H_gt; eauto 2. contradiction (ltProp_irreflexivity (hsOrd := hsOrd_vector len) l1 l1); eauto.
      + eapply eqProp_reflexivity; eauto.
      + eapply ltProp_transitivity with (y := l2); eauto.
  Qed.

  Lemma aux3_lexicographicCompare l1 l2 :
    length l1 = length l2 ->
    coq_lexicographicCompare l2 l1 = false ->
    coq_lexicographicCompare l1 l2 = false ->
    l1 = l2.
  Proof.
    rewrite redefine_coq_lexicographicCompare. intros. rewrite <- vectorEq_true_iff; eauto 2.
    change (eqb (hsEq := hsEq_vector (length l1)) l1 l2 = true). rewrite eqb_eq; eauto 2.
    pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector (length l1)) l1 l2) as [H_lt | [H_eq | H_gt]]; eauto.
    - rewrite <- ltb_lt in H_lt; eauto 2. simpl in *. congruence.
    - rewrite <- ltb_lt in H_gt; eauto 2. simpl in *. congruence.
  Qed.

  Lemma aux4_lexicographicCompare l1 l2 :
    coq_lexicographicCompare l1 l2 = true ->
    coq_equalSlices l1 l2 = false.
  Proof.
    rewrite redefine_coq_lexicographicCompare. rewrite redefine_coq_equalSlices.
    intros. eapply vectorGt_implies_not_vectorEq; eauto 2.
  Qed.

  Lemma aux5_lexicographicCompare l1 l2 :
    coq_equalSlices l1 l2 = true ->
    coq_lexicographicCompare l1 l2 = false.
  Proof.
    rewrite redefine_coq_lexicographicCompare. rewrite redefine_coq_equalSlices.
    intros. eapply vectorEq_implies_not_vectorGt; eauto 2.
  Qed.

  Lemma aux6_lexicographicCompare l1 l2 :
    length l1 = length l2 ->
    coq_lexicographicCompare l1 l2 = false ->
    (coq_lexicographicCompare l2 l1 = true \/ l1 = l2).
  Proof.
    rewrite redefine_coq_lexicographicCompare. intros.
    pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector (length l2)) l1 l2) as [H_lt | [H_eq | H_gt]]; eauto.
    - rewrite <- eqb_eq in H_eq; eauto 2. simpl in *. right; eapply aux0_equalSlices; trivial.
    - rewrite <- ltb_lt in H_gt; eauto 2. simpl in *. congruence.
  Qed.

  Lemma coq_equalOperations_comm o1 o2
    : coq_equalOperations o1 o2 = coq_equalOperations o2 o1.
  Proof.
    unfold coq_equalOperations. replace Z.eqb with (SessionPrelude.eqb (hsEq := hsEq_Z)) by reflexivity. rewrite eqb_comm; eauto.
    destruct (eqb (uint.Z o2.(Operation.Data)) (uint.Z o1.(Operation.Data))) as [ | ] eqn: H_obs; rewrite eqb_obs in H_obs; eauto.
    - do 2 rewrite andb_true_r. simpl in H_obs. generalize (o1.(Operation.VersionVector)) as v1. generalize (o2.(Operation.VersionVector)) as v2.
      induction v2 as [ | v2_hd v2_tl IH], v1 as [ | v1_hd v1_tl]; simpl; eauto.
      rewrite IH. replace Z.eqb with (SessionPrelude.eqb (hsEq := hsEq_Z)) by reflexivity. rewrite eqb_comm; eauto.
    - do 2 rewrite andb_false_r. reflexivity.
  Qed.

  Definition is_sorted (l: list Operation.t) : Prop :=
    ∀ i, ∀ j, (i < j)%nat -> ∀ o1, ∀ o2, l !! i = Some o1 -> l !! j = Some o2 ->
    coq_lexicographicCompare o2.(Operation.VersionVector) o1.(Operation.VersionVector) = true.

  Lemma redefine_is_sorted (n : nat) (l : list Operation.t)
    : is_sorted l = SessionPrelude.isSorted (hsOrd := hsOrd_Operation n) l.
  Proof.
    reflexivity.
  Defined.

  Lemma coq_maxTS_length n xs ys
    (LEN1 : length xs = n)
    (LEN2 : length ys = n)
    : length (coq_maxTS xs ys) = n.
  Proof.
    revert xs ys LEN1 LEN2; induction n as [ | n IH], xs as [ | x xs], ys as [ | y ys]; simpl in *; intros; try congruence; f_equal; eapply IH; word.
  Qed.

End properties.

Module INVARIANT.

  Variant WEAK_SERVER_INVARIANT (EXTRA: Server.t -> Prop) (s: Server.t) : Prop :=
    | WEAK_SERVER_INVARIANT_INTRO
      (PendingOperations_is_sorted: is_sorted s.(Server.PendingOperations))
      (OperationsPerformed_is_sorted: is_sorted s.(Server.OperationsPerformed))
      (EXTRA_SERVER_INVARIANT: EXTRA s)
      : WEAK_SERVER_INVARIANT EXTRA s.

  Record SERVER (EXTRA: Server.t -> Prop) (s: Server.t) : Prop :=
    SERVER_INVARIANT_INTRO
    { PendingOperations_is_sorted: is_sorted s.(Server.PendingOperations)
    ; OperationsPerformed_is_sorted: is_sorted s.(Server.OperationsPerformed)
    ; MyOperations_is_sorted: is_sorted s.(Server.MyOperations)
    ; Id_in_range: (uint.Z s.(Server.Id) >= 0)%Z /\ (uint.nat s.(Server.Id) < length s.(Server.VectorClock))%nat
    ; EXTRA_SERVER_INVARIANT: EXTRA s
    }.

  Record CLIENT (EXTRA: Client.t -> Prop) (c: Client.t) : Prop :=
    CLIENT_INVARIANT_INTRO
    { SessionSemantic_ge_0: (uint.Z c.(Client.SessionSemantic) >= 0)%Z
    ; SessionSemantic_le_5: (uint.Z c.(Client.SessionSemantic) <= 5)%Z
    ; EXTRA_CLIENT_INVARIANT: EXTRA c
    }.

End INVARIANT.

Definition FINAL_SERVER_INVARIANT {n: nat} : Server.t -> Prop :=
  let EXTRA_SERVER_INVARIANT (s: Server.t) : Prop :=
    (uint.nat s.(Server.Id) < n)%nat /\
    (uint.nat s.(Server.NumberOfServers) = n)%nat /\
    (length s.(Server.OperationsPerformed) = n)%nat /\
    (length s.(Server.OperationsPerformed) = n)%nat /\
    (length s.(Server.GossipAcknowledgements) = n)%nat (* /\
    Forall (fun a : nat => a <= s.(Server.MyOperations))%nat s.(Server.GossipAcknowledgements) *)
  in
  SERVER_INVARIANT EXTRA_SERVER_INVARIANT.

Notation WEAK_SERVER_INVARIANT := INVARIANT.WEAK_SERVER_INVARIANT.
Notation SERVER_INVARIANT := INVARIANT.SERVER.
Notation CLIENT_INVARIANT := INVARIANT.CLIENT.

Section heap.
  Context `{hG: !heapGS Σ}.

  Lemma Operation_wf_INTRO o opv (n : nat)
    : (is_operation opv o n)%I ⊢@{iProp Σ} (⌜Operation_wf n o⌝)%I.
  Proof.
    iIntros "H_hd". iDestruct "H_hd" as "(%H1 & [%H2 %H4]  & H3)"; iClear "H3".
    iPureIntro; split; [eapply SessionPrelude.Forall_True | done].
  Qed.

  Lemma Forall_Operation_wf l ops (n: nat)
    : ([∗ list] opv;o ∈ ops;l, is_operation opv o n)%I ⊢@{iProp Σ} (⌜Forall (Operation_wf n) l⌝)%I.
  Proof.
    revert ops; induction l as [ | hd tl IH]; intros ops.
    - iIntros "H_big_sepL2"; iPureIntro; eauto.
    - iIntros "H_big_sepL2"; iPoseProof (big_sepL2_cons_inv_r with "H_big_sepL2") as "(%hd' & %tl' & -> & H_hd & H_tl)".
      iDestruct "H_hd" as "(%H1 & %H2 & H3)"; iClear "H3".
      iAssert ⌜Forall (Operation_wf n) tl⌝%I as "%YES1".
      { iApply IH; iExact "H_tl". }
      iPureIntro; econstructor; trivial.
      destruct H2 as [H2 H2']; split; [eapply SessionPrelude.Forall_True | done].
  Qed.

  Lemma op_versionVector_len (s: Slice.t) (l: list Operation.t) (n: nat)
    : (operation_slice s l n)%I ⊢@{iProp Σ} (⌜∀ i : nat, ∀ e, l !! i = Some e -> length e.(Operation.VersionVector) = n⌝)%I.
  Proof.
    iIntros "(%ops & H_ops & H)".
    iPoseProof (Forall_Operation_wf with "H") as "%H_well_formed".
    pose proof (List.Forall_forall (Operation_wf n) l) as claim.
    rewrite claim in H_well_formed; iPureIntro; intros i x H_x.
    enough (WTS : Operation_wf n x) by now red in WTS.
    eapply H_well_formed; eapply SessionPrelude.lookup_In; eauto.
  Qed.

  Lemma pers_is_operation opv o (n: nat)
    : (is_operation opv o n)%I ⊢@{iProp Σ} (<pers> (is_operation opv o n))%I.
  Proof.
    iIntros "#H"; done.
  Qed.

  Lemma pers_big_sepL2_is_operation l ops (n: nat)
    : ([∗ list] opv;o ∈ ops;l, is_operation opv o n)%I ⊢@{iProp Σ} (<pers> ([∗ list] opv;o ∈ ops;l, is_operation opv o n))%I.
  Proof.
    iIntros "H_big_sepL2"; iApply (big_sepL2_persistently).
    iApply (big_sepL2_mono (λ k, λ y1, λ y2, is_operation y1 y2 n)%I with "[$H_big_sepL2]").
    intros; iIntros "#H"; done.
  Qed.

  Lemma pers_emp
    : (emp)%I ⊢@{iProp Σ} (<pers> emp)%I.
  Proof.
    iIntros "#H"; done.
  Qed.

  Lemma big_sepL2_is_operation_elim (l: list Operation.t) (ops: list (Slice.t * w64)) (n: nat) (i: nat) l_i ops_i
    (H_l_i: l !! i = Some l_i)
    (H_ops_i: ops !! i = Some ops_i)
    : ([∗ list] opv;o ∈ ops;l, is_operation opv o n)%I ⊢@{iProp Σ} (is_operation ops_i l_i n)%I.
  Proof.
    rewrite <- take_drop with (l := l) (i := i); rewrite <- take_drop with (l := ops) (i := i); iIntros "H". 
    assert (i < length l)%nat as H1_i by now eapply lookup_lt_is_Some_1.
    assert (i < length ops)%nat as H2_i by now eapply lookup_lt_is_Some_1.  
    iAssert (([∗ list] opv;o ∈ take i ops;take i l, is_operation opv o n) ∗ ([∗ list] opv;o ∈ drop i ops;drop i l, is_operation opv o n))%I with "[H]" as "[H1 H2]".
    { iApply (big_sepL2_app_equiv with "H"); do 2 rewrite length_take; word. }
    destruct (drop i ops) as [ | ops_i' ops_suffix] eqn: H_ops_suffix.
    { apply f_equal with (f := length) in H_ops_suffix; simpl in *; rewrite length_drop in H_ops_suffix. word. }
    iPoseProof (big_sepL2_cons_inv_l with "[$H2]") as "(%l_i' & %l_suffix & %H_l_suffix & H3 & H4)".
    rewrite <- take_drop with (l := l) (i := i) in H_l_i; rewrite <- take_drop with (l := ops) (i := i) in H_ops_i.
    rewrite H_l_suffix in H_l_i; rewrite H_ops_suffix in H_ops_i.
    assert (i = length (take i l)) as H3_i.
    { rewrite length_take; word. }
    assert (i = length (take i ops)) as H4_i.
    { rewrite length_take; word. }
    pose proof (list_lookup_middle (take i l) l_suffix l_i' i H3_i) as EQ_l_i.
    pose proof (list_lookup_middle (take i ops) ops_suffix ops_i' i H4_i) as EQ_ops_i.
    assert (l_i = l_i') as <- by congruence.
    assert (ops_i = ops_i') as <- by congruence.
    iExact "H3".
  Qed.

  Lemma big_sepL2_is_operation_intro (l: list Operation.t) (ops: list (Slice.t * w64)) (n: nat)
    (LENGTH: length l = length ops)
    : (∀ i : nat, ∀ l_i, ∀ ops_i, ⌜(l !! i = Some l_i) /\ (ops !! i = Some ops_i)⌝ -∗ is_operation ops_i l_i n)%I ⊢@{iProp Σ} ([∗ list] opv;o ∈ ops;l, is_operation opv o n)%I.
  Proof.
    revert ops n LENGTH; induction l as [ | l_hd l_tl IH], ops as [ | ops_hd ops_tl]; intros; simpl in *; try congruence.
    - iIntros "#H"; iClear "H"; done.
    - iIntros "#H"; iSplit.
      + iApply "H"; instantiate (1 := 0%nat); done.
      + iApply IH. { word. }
        iIntros "%i %l_i %ops_i [%H_l_i %H_ops_i]"; iApply "H"; instantiate (1 := S i); done.
  Qed.

  Lemma big_sepL2_middle_split {A: Type} {B: Type} {Φ: A -> B -> iProp Σ} {xs: list A} {i: nat} {x0: A} (ys: list B)
    (LOOKUP: xs !! i = Some x0)
    : ([∗ list] x;y ∈ xs;ys, Φ x y)%I ⊢@{iProp Σ} (∃ y0, ∃ ys1, ∃ ys2, ⌜ys = (ys1 ++ y0 :: ys2)%list /\ length ys1 = i⌝ ∗ Φ x0 y0 ∗ ([∗ list] x;y ∈ take i xs;ys1, Φ x y) ∗ ([∗ list] x;y ∈ drop (i + 1)%nat xs;ys2, Φ x y))%I.
  Proof.
    pose proof (take_drop_middle xs i x0 LOOKUP) as claim1.
    assert (i < length xs)%nat as claim2.
    { now eapply lookup_lt_is_Some_1. }
    iIntros "H_big_sepL2".
    iPoseProof (big_sepL2_length with "[$H_big_sepL2]") as "%LENGTH".
    rewrite <- take_drop with (l := xs) (i := i).
    rewrite <- take_drop with (l := ys) (i := i).
    iPoseProof (big_sepL2_app_equiv with "H_big_sepL2") as "[H_prefix H_suffix]".
    { (do 2 rewrite length_take); word. }
    assert (is_Some (ys !! i)) as [y0 H_y0].
    { eapply lookup_lt_is_Some_2; word. }
    iExists y0; iExists (take i ys); iExists (drop (S i) ys).
    pose proof (take_drop_middle ys i y0 H_y0) as claim3.
    iSplitL "".
    { iPureIntro; split; [rewrite claim3; eapply take_drop | rewrite length_take; word]. }
    rewrite <- take_drop with (l := ys) (i := i) in claim3 at -1.
    apply SessionPrelude.app_cancel_l in claim3; rewrite take_drop in claim3; rewrite <- claim3.
    iPoseProof (big_sepL2_cons_inv_r with "[$H_suffix]") as "(%x0' & %xs2 & %EQ & H_middle & H_suffix)".
    rewrite <- take_drop with (l := xs) (i := i) in claim1 at -1.
    apply SessionPrelude.app_cancel_l in claim1; rewrite take_drop in claim1.
    assert (x0' = x0) as -> by congruence.
    iSplitL "H_middle".
    { iExact "H_middle". }
    rewrite take_drop; iSplitL "H_prefix".
    { iExact "H_prefix". }
    { rewrite <- drop_drop with (l := xs) (n1 := 1%nat) (n2 := i); rewrite -> EQ; iExact "H_suffix". }
  Qed.

  Lemma big_sepL2_middle_merge {A: Type} {B: Type} {Φ: A -> B -> iProp Σ} {xs: list A} {i: nat} {x0: A} (y0: B) (ys1: list B) (ys2: list B)
    (LOOKUP: xs !! i = Some x0)
    : (Φ x0 y0 ∗ ([∗ list] x;y ∈ take i xs;ys1, Φ x y) ∗ ([∗ list] x;y ∈ drop (i + 1)%nat xs;ys2, Φ x y))%I ⊢@{iProp Σ} ([∗ list] x;y ∈ xs;(ys1 ++ y0 :: ys2)%list, Φ x y)%I.
  Proof.
    pose proof (take_drop_middle xs i x0 LOOKUP) as claim1.
    assert (i < length xs)%nat as claim2.
    { now eapply lookup_lt_is_Some_1. }
    iIntros "(H_middle & H_prefix & H_suffix)".
    replace ([∗ list] x;y ∈ xs;(ys1 ++ y0 :: ys2), Φ x y)%I with ([∗ list] x;y ∈ take i xs ++ x0 :: drop (S i) xs;(ys1 ++ y0 :: ys2), Φ x y)%I by now rewrite claim1.
    rewrite <- drop_drop with (l := xs) (n1 := 1%nat) (n2 := i).
    rewrite <- take_drop with (l := xs) (i := i) in claim1 at -1.
    apply SessionPrelude.app_cancel_l in claim1; rewrite take_drop in claim1.
    rewrite <- claim1; simpl; replace (drop 0 (drop (S i) xs)) with (drop (S i) xs) by reflexivity.
    iApply (big_sepL2_app with "[$H_prefix] [H_middle H_suffix]"); simpl; iFrame.
  Qed.

End heap.
