From Perennial.program_proof.session Require Export coq_session coq_session_client.

Reserved Infix "=~=" (at level 70, no associativity).

Class Similarity (A : Type) (B : Type) : Type :=
  is_similar_to (x : A) (y : B) : Prop.

Infix "=~=" := is_similar_to.

#[global]
Instance Similarity_fun {D : Type} {D' : Type} {C : Type} {C' : Type} (D_SIM : Similarity D D') (C_SIM : Similarity C C') : Similarity (D -> C) (D' -> C') :=
  fun f : D -> C => fun f' : D' -> C' => forall x, forall x', x =~= x' -> f x =~= f' x'.

#[global]
Instance Similarity_prod {A : Type} {A' : Type} {B : Type} {B' : Type} (SIM1 : Similarity A A') (SIM2 : Similarity B B') : Similarity (A * B) (A' * B') :=
  fun p : A * B => fun p' : A' * B' => fst p =~= fst p' /\ snd p =~= snd p'.

Inductive list_corres {A : Type} {B : Type} {SIM : Similarity A B} : Similarity (list A) (list B) :=
  | nil_corres
    : [] =~= []
  | cons_corres x y xs ys
    (head_corres : x =~= y)
    (tail_corres : xs =~= ys)
    : x :: xs =~= y :: ys.

#[global]
Instance Similarity_list {A : Type} {B : Type} (SIM : Similarity A B) : Similarity (list A) (list B) :=
  @list_corres A B SIM.

Lemma Similarity_list_length {A : Type} {B : Type} {SIM : Similarity A B} (xs : list A) (ys : list B)
  (H_sim : xs =~= ys)
  : length xs = length ys.
Proof.
  induction H_sim as [ | ? ? ? ? ? ? IH]; simpl; congruence.
Qed.

Lemma fold_left_corres {A : Type} {A' : Type} {B : Type} {B' : Type} {A_SIM : Similarity A A'} {B_SIM : Similarity B B'} (f : A -> B -> A) (xs : list B) (z : A) (f' : A' -> B' -> A') (xs' : list B') (z' : A')
  (f_corres : f =~= f')
  (xs_corres : xs =~= xs')
  (z_corres : z =~= z')
  : fold_left f xs z =~= fold_left f' xs' z'.
Proof.
  revert z z' z_corres. induction xs_corres as [ | ? ? ? ? ? ? IH]; simpl; eauto.
  intros ? ? ?; eapply IH. eapply f_corres; [exact z_corres | exact head_corres].
Qed.

Definition UPPER_BOUND : Z :=
  2 ^ 64.

#[global]
Instance Similarity_u64 : Similarity u64 nat :=
  fun u => fun n => (n = uint.nat u)%nat /\ (uint.Z u >= 0 /\ uint.Z u < UPPER_BOUND)%Z.

Lemma Similarity_u64_range (u : u64) (n : nat)
  (H_sim : u =~= n)
  : (uint.Z u >= 0 /\ uint.Z u < UPPER_BOUND)%Z.
Proof.
  do 2 red in H_sim. word.
Qed.

#[global]
Instance Similarity_bool : Similarity bool bool :=
  @eq bool.

Module Operation'.

  Record t : Set :=
    mk
    { VersionVector : list nat
    ; Data : nat
    }.

  Record corres (op : Operation.t) (op' : Operation'.t) : Prop :=
    Similarity_Operation_INTRO
    { VersionVector_corres : op.(Operation.VersionVector) =~= op'.(VersionVector)
    ; Data_corres : op.(Operation.Data) =~= op'.(Data)
    }.

End Operation'.

#[global]
Instance Similarity_Operation : Similarity Operation.t Operation'.t :=
  Operation'.corres.

Module Message'.

  Record t : Set :=
    mk
    { MessageType : nat
    ; C2S_Client_Id : nat
    ; C2S_Server_Id : nat
    ; C2S_Client_OperationType : nat
    ; C2S_Client_Data : nat
    ; C2S_Client_VersionVector : list nat
    ; S2S_Gossip_Sending_ServerId : nat
    ; S2S_Gossip_Receiving_ServerId : nat
    ; S2S_Gossip_Operations : list Operation'.t
    ; S2S_Gossip_Index : nat
    ; S2S_Acknowledge_Gossip_Sending_ServerId : nat
    ; S2S_Acknowledge_Gossip_Receiving_ServerId : nat
    ; S2S_Acknowledge_Gossip_Index : nat
    ; S2C_Client_OperationType : nat
    ; S2C_Client_Data : nat
    ; S2C_Client_VersionVector : list nat
    ; S2C_Server_Id : nat
    ; S2C_Client_Number : nat
    }.

  Record corres (msg : Message.t) (msg' : Message'.t) : Prop :=
    Similarity_Message_INTRO
    { MessageType_corres : msg.(Message.MessageType) =~= msg'.(MessageType)
    ; C2S_Client_Id_corres : msg.(Message.C2S_Client_Id) =~= msg'.(C2S_Client_Id)
    ; C2S_Server_Id_corres : msg.(Message.C2S_Server_Id) =~= msg'.(C2S_Server_Id)
    ; C2S_Client_OperationType_corres : msg.(Message.C2S_Client_OperationType) =~= msg'.(C2S_Client_OperationType)
    ; C2S_Client_Data_corres_corres : msg.(Message.C2S_Client_Data) =~= msg'.(C2S_Client_Data)
    ; C2S_Client_VersionVector_corres : msg.(Message.C2S_Client_VersionVector) =~= msg'.(C2S_Client_VersionVector)
    ; S2S_Gossip_Sending_ServerId_corres : msg.(Message.S2S_Gossip_Sending_ServerId) =~= msg'.(S2S_Gossip_Sending_ServerId)
    ; S2S_Gossip_Receiving_ServerId_corres : msg.(Message.S2S_Gossip_Receiving_ServerId) =~= msg'.(S2S_Gossip_Receiving_ServerId)
    ; S2S_Gossip_Operations_corres : msg.(Message.S2S_Gossip_Operations) =~= msg'.(S2S_Gossip_Operations)
    ; S2S_Gossip_Index_corres : msg.(Message.S2S_Gossip_Index) =~= msg'.(S2S_Gossip_Index)
    ; S2S_Acknowledge_Gossip_Sending_ServerId_corres : msg.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) =~= msg'.(S2S_Acknowledge_Gossip_Sending_ServerId)
    ; S2S_Acknowledge_Gossip_Receiving_ServerId_corres : msg.(Message.S2S_Acknowledge_Gossip_Receiving_ServerId) =~= msg'.(S2S_Acknowledge_Gossip_Receiving_ServerId)
    ; S2S_Acknowledge_Gossip_Index_corres : msg.(Message.S2S_Acknowledge_Gossip_Index) =~= msg'.(S2S_Acknowledge_Gossip_Index)
    ; S2C_Client_OperationType_corres : msg.(Message.S2C_Client_OperationType) =~= msg'.(S2C_Client_OperationType)
    ; S2C_Client_Data_corres : msg.(Message.S2C_Client_Data) =~= msg'.(S2C_Client_Data)
    ; S2C_Client_VersionVector_corres : msg.(Message.S2C_Client_VersionVector) =~= msg'.(S2C_Client_VersionVector)
    ; S2C_Server_Id_corres : msg.(Message.S2C_Server_Id) =~= msg'.(S2C_Server_Id)
    ; S2C_Client_Number_corres : msg.(Message.S2C_Client_Number) =~= msg'.(S2C_Client_Number)
    }.

End Message'.

#[global]
Instance Similarity_Message : Similarity Message.t Message'.t :=
  Message'.corres.

Module Server'.

  Record t : Set :=
    mk
    { Id : nat
    ; NumberOfServers : nat
    ; UnsatisfiedRequests : list Message'.t
    ; VectorClock : list nat
    ; OperationsPerformed : list Operation'.t
    ; MyOperations : list Operation'.t
    ; PendingOperations : list Operation'.t
    ; GossipAcknowledgements : list nat
    }.

  Record corres (server : Server.t) (server' : Server'.t) : Prop :=
    Similarity_Server_INTRO
    { Id_corres : server.(Server.Id) =~= server'.(Id)
    ; NumberOfServers_corres : server.(Server.NumberOfServers) =~= server'.(NumberOfServers)
    ; UnsatisfiedRequests_corres : server.(Server.UnsatisfiedRequests) =~= server'.(UnsatisfiedRequests)
    ; VectorClock_corres : server.(Server.VectorClock) =~= server'.(VectorClock)
    ; OperationsPerformed_corres : server.(Server.OperationsPerformed) =~= server'.(OperationsPerformed)
    ; MyOperations_corres : server.(Server.MyOperations) =~= server'.(MyOperations)
    ; PendingOperations_corres : server.(Server.PendingOperations) =~= server'.(PendingOperations)
    ; GossipAcknowledgements_corres : server.(Server.GossipAcknowledgements) =~= server'.(GossipAcknowledgements)
    }.

End Server'.

#[global]
Instance Similarity_Server : Similarity Server.t Server'.t :=
  Server'.corres.

Module Client'.

  Record t : Set :=
    mk
    { Id : nat
    ; NumberOfServers : nat
    ; WriteVersionVector : list nat
    ; ReadVersionVector : list nat
    ; SessionSemantic : nat
    }.

  Record corres (client : Client.t) (client' : Client'.t) : Prop :=
    Similarity_Client_INTRO
    { Id_corres : client.(Client.Id) =~= client'.(Id)
    ; NumberOfServers_corres : client.(Client.NumberOfServers) =~= client'.(NumberOfServers)
    ; WriteVersionVector_corres : client.(Client.WriteVersionVector) =~= client'.(WriteVersionVector)
    ; ReadVersionVector_corres : client.(Client.ReadVersionVector) =~= client'.(ReadVersionVector)
    ; SessionSemantic_corres : client.(Client.SessionSemantic) =~= client'.(SessionSemantic)
    }.

End Client'.

#[global]
Instance Similarity_Client : Similarity Client.t Client'.t :=
  Client'.corres.

Module NatImplServer.

  Fixpoint coq_compareVersionVector (v1 : list nat) (v2 : list nat) : bool :=
    match v1 with
    | [] => true
    | h1 :: t1 =>
      match v2 with
      | [] => true
      | h2 :: t2 => negb (h1 <? h2)%nat && coq_compareVersionVector t1 t2
      end
    end.

  Fixpoint coq_lexicographicCompare (v1 : list nat) (v2 : list nat) : bool :=
    match v1 with
    | [] => false 
    | h1 :: t1 =>
      match v2 with
      | [] => false 
      | h2 :: t2 => if (h1 =? h2)%nat then coq_lexicographicCompare t1 t2 else (h1 >? h2)%nat
      end
    end.

  Definition coq_maxTwoInts (x : nat) (y : nat) : nat :=
    if (x >? y)%nat then x else y. 

  Fixpoint coq_maxTS (v1 : list nat) (v2 : list nat) : list nat :=
    match v1 with
    | [] => []
    | h1 :: t1 =>
      match v2 with
      | [] => [] 
      | h2 :: t2 => coq_maxTwoInts h1 h2 :: coq_maxTS t1 t2
      end
    end.

  Definition coq_oneOffVersionVector (v1 : list nat) (v2 : list nat) : bool :=
    let loop_init : bool * bool :=
      (true, true)
    in
    let loop_step (acc : bool * bool) (element : nat * nat) : bool * bool :=
      let (e1, e2) := element in
      let (output, canApply) := acc in
      if canApply && (e1 + 1 =? e2)%nat then (output, false) else ((e1 >=? e2)%nat && output, canApply)
    in
    let (output, canApply) := fold_left loop_step (zip v1 v2) loop_init in
    output && negb canApply.

  Fixpoint coq_equalSlices (s1 : list nat) (s2 : list nat) : bool :=
    match s1 with
    | [] => true
    | h1 :: t1 => 
      match s2 with
      | [] => true
      | h2 :: t2 => (h1 =? h2)%nat && coq_equalSlices t1 t2
      end
    end.

  Definition coq_equalOperations (o1 : Operation'.t) (o2 : Operation'.t) : bool :=
    coq_equalSlices o1.(Operation'.VersionVector) o2.(Operation'.VersionVector) && (o1.(Operation'.Data) =? o2.(Operation'.Data))%nat.

  Fixpoint coq_sortedInsert (l : list Operation'.t) (i : Operation'.t) : list Operation'.t :=
    match l with
    | [] => [i]
    | h :: t => if coq_lexicographicCompare h.(Operation'.VersionVector) i.(Operation'.VersionVector) || coq_equalSlices h.(Operation'.VersionVector) i.(Operation'.VersionVector) then (i :: h :: t)%list else (h :: coq_sortedInsert t i)%list
    end.

  Definition coq_mergeOperations (l1 : list Operation'.t) (l2 : list Operation'.t) : list Operation'.t :=
    let output := fold_left coq_sortedInsert l2 l1 in
    let loop_init : nat * list Operation'.t :=
      (0%nat, [])
    in
    let loop_step (acc : nat * list Operation'.t) (element : Operation'.t) : nat * list Operation'.t :=
      let (index, acc) := acc in
      match output !! (index + 1)%nat with
      | Some v => if coq_equalOperations element v then ((index + 1)%nat, acc) else ((index + 1)%nat, acc ++ [element])
      | None => ((index + 1)%nat, acc ++ [element])
      end
    in
    snd (fold_left loop_step output loop_init).

  Definition coq_deleteAtIndexOperation (o : list Operation'.t) (index : nat) : list Operation'.t :=
    take index o ++ drop (index + 1) o.

  Definition coq_deleteAtIndexMessage (m : list Message'.t) (index : nat) : list Message'.t :=
    take index m ++ drop (index + 1) m.

  Definition coq_getDataFromOperationLog (l : list Operation'.t) : nat :=
    match l !! (length l - 1)%nat with
    | Some v => v.(Operation'.Data)
    | None => 0%nat
    end.

  Definition coq_receiveGossip (s : Server'.t) (r : Message'.t) : Server'.t :=
    if (length r.(Message'.S2S_Gossip_Operations) =? 0)%nat then
      s
    else
      let focus := coq_mergeOperations s.(Server'.PendingOperations) r.(Message'.S2S_Gossip_Operations) in
      let loop_init : nat * Server'.t :=
        (0%nat, Server'.mk s.(Server'.Id) s.(Server'.NumberOfServers) s.(Server'.UnsatisfiedRequests) s.(Server'.VectorClock) s.(Server'.OperationsPerformed) s.(Server'.MyOperations) focus s.(Server'.GossipAcknowledgements))
      in
      let loop_step (acc : nat * Server'.t) (e : Operation'.t) : nat * Server'.t :=
        let '(i, s) := acc in
        if coq_oneOffVersionVector s.(Server'.VectorClock) e.(Operation'.VersionVector) then
          let OperationsPerformed := coq_mergeOperations s.(Server'.OperationsPerformed) [e] in
          let VectorClock := coq_maxTS s.(Server'.VectorClock) e.(Operation'.VersionVector) in
          let PendingOperations := coq_deleteAtIndexOperation s.(Server'.PendingOperations) i in
          (i, Server'.mk s.(Server'.Id) s.(Server'.NumberOfServers) s.(Server'.UnsatisfiedRequests) VectorClock OperationsPerformed s.(Server'.MyOperations) PendingOperations s.(Server'.GossipAcknowledgements))
        else ((i + 1)%nat, s)
      in
      snd (fold_left loop_step focus loop_init).

  Definition coq_acknowledgeGossip (s : Server'.t) (r : Message'.t) : Server'.t :=
    let i := r.(Message'.S2S_Acknowledge_Gossip_Sending_ServerId) in
    let l := s.(Server'.GossipAcknowledgements) in
    if (i >=? length l)%nat then
      s
    else
      let prevGossipAcknowledgementsValue : nat :=
        match s.(Server'.GossipAcknowledgements) !! i with
        | Some x => x
        | None => 0%nat
        end
      in
      let newGossipAcknowledgements := coq_maxTwoInts prevGossipAcknowledgementsValue r.(Message'.S2S_Acknowledge_Gossip_Index) in
      let gossipAcknowledgements := <[i := newGossipAcknowledgements]> l in
      Server'.mk s.(Server'.Id) s.(Server'.NumberOfServers) s.(Server'.UnsatisfiedRequests) s.(Server'.VectorClock) s.(Server'.OperationsPerformed) s.(Server'.MyOperations) s.(Server'.PendingOperations) gossipAcknowledgements.

  Definition coq_getGossipOperations (s : Server'.t) (serverId : nat) : list Operation'.t :=
    match s.(Server'.GossipAcknowledgements) !! serverId with
    | Some v => drop v s.(Server'.MyOperations)
    | None => []
    end.

  Definition coq_processClientRequest (s : Server'.t) (r : Message'.t) : bool * Server'.t * Message'.t :=
    if negb (coq_compareVersionVector s.(Server'.VectorClock) r.(Message'.C2S_Client_VersionVector)) then
      (false, s, (Message'.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0))
    else
      if (r.(Message'.C2S_Client_OperationType) =? 0)%nat then
        let S2C_Client_Data := coq_getDataFromOperationLog s.(Server'.OperationsPerformed) in
        let S2C_Client_VersionVector := s.(Server'.VectorClock) in
        let S2C_Client_Number := r.(Message'.C2S_Client_Id) in
        let S2C_Server_Id := s.(Server'.Id) in
        (true, s, (Message'.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 0 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number))
      else
        let v := list_lookup_total s.(Server'.Id) s.(Server'.VectorClock) in
        let VectorClock := <[s.(Server'.Id) := (v + 1)%nat]> s.(Server'.VectorClock) in
        let OperationsPerformed := coq_sortedInsert s.(Server'.OperationsPerformed) (Operation'.mk VectorClock r.(Message'.C2S_Client_Data)) in
        let MyOperations := coq_sortedInsert s.(Server'.MyOperations) (Operation'.mk VectorClock r.(Message'.C2S_Client_Data)) in
        let S2C_Client_OperationType := 1%nat in
        let S2C_Client_Data := 0%nat in
        let S2C_Client_VersionVector := VectorClock in
        let S2C_Client_Number := r.(Message'.C2S_Client_Id) in
        let S2C_Server_Id := s.(Server'.Id) in
        (true, Server'.mk s.(Server'.Id) s.(Server'.NumberOfServers) s.(Server'.UnsatisfiedRequests) VectorClock OperationsPerformed MyOperations s.(Server'.PendingOperations) s.(Server'.GossipAcknowledgements), (Message'.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 1 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number)).

  Definition coq_processRequest (server : Server'.t) (request : Message'.t) : Server'.t * list Message'.t :=
    match request.(Message'.MessageType) with
    | 0%nat =>
      let '(succeeded, server, reply) := coq_processClientRequest server request in
      if succeeded then
        (server, [reply])
      else
        let UnsatisfiedRequests := server.(Server'.UnsatisfiedRequests) ++ [request] in 
        let server := Server'.mk server.(Server'.Id) server.(Server'.NumberOfServers) UnsatisfiedRequests server.(Server'.VectorClock) server.(Server'.OperationsPerformed) server.(Server'.MyOperations) server.(Server'.PendingOperations) server.(Server'.GossipAcknowledgements) in
        (server, [])
    | 1%nat =>
      let server := coq_receiveGossip server request in
      let focus := server.(Server'.UnsatisfiedRequests) in
      let loop_init : nat * (Server'.t * list Message'.t) :=
        (0%nat, (server, [Message'.mk 2 0 0 0 0 [] 0 0 [] 0 (server.(Server'.Id)) (request.(Message'.S2S_Gossip_Sending_ServerId)) (request.(Message'.S2S_Gossip_Index)) 0 0 [] 0 0]))
      in
      let loop_step (acc : nat * (Server'.t * list Message'.t)) (element : Message'.t) : nat * (Server'.t * list Message'.t) :=
        let '(i, (s, outGoingRequests)) := acc in
        let '(succeeded, s, reply) := coq_processClientRequest s element in
        if succeeded then
          let UnsatisfiedRequests := coq_deleteAtIndexMessage s.(Server'.UnsatisfiedRequests) i in
          (i, (Server'.mk s.(Server'.Id) s.(Server'.NumberOfServers) UnsatisfiedRequests s.(Server'.VectorClock) s.(Server'.OperationsPerformed) s.(Server'.MyOperations) s.(Server'.PendingOperations) s.(Server'.GossipAcknowledgements), outGoingRequests ++ [reply]))
        else
          ((i + 1)%nat, (s, outGoingRequests))
      in
      snd (fold_left loop_step focus loop_init)
    | 2%nat => (coq_acknowledgeGossip server request, [])
    | 3%nat =>
      let loop_init : list Message'.t :=
        []
      in
      let loop_step (acc : list Message'.t) (index : nat) : list Message'.t :=
        if negb (index =? server.(Server'.Id))%nat && negb (length (coq_getGossipOperations server index) =? 0)%nat then
          let S2S_Gossip_Sending_ServerId := server.(Server'.Id) in
          let S2S_Gossip_Receiving_ServerId := index in
          let S2S_Gossip_Operations := coq_getGossipOperations server index in
          let S2S_Gossip_Index := length server.(Server'.MyOperations) in
          let message := Message'.mk 1 0 0 0 0 [] S2S_Gossip_Sending_ServerId S2S_Gossip_Receiving_ServerId S2S_Gossip_Operations S2S_Gossip_Index 0 0 0 0 0 [] 0 0 in
          acc ++ [message]
        else
          acc
      in
      (server, fold_left loop_step (seq 0%nat (uint.nat server.(Server'.NumberOfServers))) loop_init)
    | _ => (server, [])
    end.

  Section EQUIVALENCE.

    Lemma coq_compareVersionVector_corres
      : CoqSessionServer.coq_compareVersionVector =~= coq_compareVersionVector.
    Admitted.
  
    Lemma coq_lexicographicCompare_corres
      : CoqSessionServer.coq_lexicographicCompare =~= coq_lexicographicCompare.
    Admitted.
  
    Lemma coq_maxTwoInts_corres
      : CoqSessionServer.coq_maxTwoInts =~= coq_maxTwoInts.
    Admitted.
  
    Lemma coq_maxTS_corres
      : CoqSessionServer.coq_maxTS =~= coq_maxTS.
    Admitted.
  
    Lemma coq_oneOffVersionVector_corres
      : CoqSessionServer.coq_oneOffVersionVector =~= coq_oneOffVersionVector.
    Admitted.
  
    Lemma coq_equalSlices_corres
      : CoqSessionServer.coq_equalSlices =~= coq_equalSlices.
    Admitted.
  
    Lemma coq_equalOperations_corres
      : CoqSessionServer.coq_equalOperations =~= coq_equalOperations.
    Admitted.
  
    Lemma coq_sortedInsert_corres
      : CoqSessionServer.coq_sortedInsert =~= coq_sortedInsert.
    Admitted.
  
    Lemma coq_mergeOperations_corres
      : CoqSessionServer.coq_mergeOperations =~= coq_mergeOperations.
    Admitted.
  
    Lemma coq_deleteAtIndexOperation_corres
      : CoqSessionServer.coq_deleteAtIndexOperation =~= coq_deleteAtIndexOperation.
    Admitted.
  
    Lemma coq_deleteAtIndexMessage_corres
      : CoqSessionServer.coq_deleteAtIndexMessage =~= coq_deleteAtIndexMessage.
    Admitted.
  
    Lemma coq_getDataFromOperationLog_corres
      : CoqSessionServer.coq_getDataFromOperationLog =~= coq_getDataFromOperationLog.
    Admitted.
  
    Lemma coq_receiveGossip_corres
      : CoqSessionServer.coq_receiveGossip =~= coq_receiveGossip.
    Admitted.
  
    Lemma coq_acknowledgeGossip_corres
      : CoqSessionServer.coq_acknowledgeGossip =~= coq_acknowledgeGossip.
    Admitted.

    Lemma coq_getGossipOperations_corres
      : CoqSessionServer.coq_getGossipOperations =~= coq_getGossipOperations.
    Admitted.

    Lemma coq_processClientRequest_corres
      : CoqSessionServer.coq_processClientRequest =~= coq_processClientRequest.
    Admitted.
  
    Lemma coq_processRequest_corres
      : CoqSessionServer.coq_processRequest =~= coq_processRequest.
    Admitted.

  End EQUIVALENCE.

End NatImplServer.

Export NatImplServer.

Module NatImplClient.

  Definition coq_read (c : Client'.t) (serverId : nat) : Message'.t :=
    match c.(Client'.SessionSemantic) with
    | 0%nat => Message'.mk 0 c.(Client'.Id) serverId 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 1%nat => Message'.mk 0 c.(Client'.Id) serverId 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 2%nat => Message'.mk 0 c.(Client'.Id) serverId 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 3%nat => Message'.mk 0 c.(Client'.Id) serverId 0 0 c.(Client'.ReadVersionVector) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 4%nat => Message'.mk 0 c.(Client'.Id) serverId 0 0 c.(Client'.WriteVersionVector) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 5%nat => Message'.mk 0 c.(Client'.Id) serverId 0 0 (coq_maxTS c.(Client'.WriteVersionVector) c.(Client'.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | _ => Message'.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    end.

  Definition coq_write (c : Client'.t) (serverId : nat) (value : nat) : Message'.t :=
    match c.(Client'.SessionSemantic) with
    | 0%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 1%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value c.(Client'.ReadVersionVector) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 2%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value c.(Client'.WriteVersionVector) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 3%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 4%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 5%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value (coq_maxTS c.(Client'.WriteVersionVector) c.(Client'.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | _ => Message'.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    end.

  Definition coq_processRequest (c : Client'.t) (requestType : nat) (serverId : nat) (value : nat) (ackMessage : Message'.t) : Client'.t * Message'.t :=
    match requestType with
    | 0%nat => (c, coq_read c serverId)
    | 1%nat => (c, coq_write c serverId value)
    | 2%nat =>
      match ackMessage.(Message'.S2C_Client_OperationType) with
      | 0%nat => (Client'.mk c.(Client'.Id) c.(Client'.NumberOfServers) c.(Client'.WriteVersionVector) ackMessage.(Message'.S2C_Client_VersionVector) c.(Client'.SessionSemantic), Message'.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
      | 1%nat => (Client'.mk c.(Client'.Id) c.(Client'.NumberOfServers) (ackMessage.(Message'.S2C_Client_VersionVector)) c.(Client'.ReadVersionVector) c.(Client'.SessionSemantic), Message'.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
      | _ => (c, Message'.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
      end
    | _ => (c, Message'.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
    end.

  Section EQUIVALENCE.

    Lemma coq_read_corres
      : CoqSessionClient.coq_read =~= coq_read.
    Admitted.

    Lemma coq_write_corres
      : CoqSessionClient.coq_write =~= coq_write.
    Admitted.
  
    Lemma coq_processRequest_corres
      : CoqSessionClient.coq_processRequest =~= coq_processRequest.
    Admitted.

  End EQUIVALENCE.

End NatImplClient.

Export NatImplClient.
