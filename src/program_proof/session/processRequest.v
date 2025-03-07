From Perennial.program_proof.session Require Export session_prelude coq_session.
From Perennial.program_proof.session Require Export versionVector processClientRequest gossip.

Definition coq_processClientRequest (s: Server.t) (r: Message.t) :
  (bool * Server.t * Message.t) :=
  if (negb (coq_compareVersionVector s.(Server.VectorClock) r.(Message.C2S_Client_VersionVector))) then
    (false, s, (Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0))
  else
    if (uint.nat r.(Message.C2S_Client_OperationType) =? 0) then
      let S2C_Client_Data : u64 := coq_getDataFromOperationLog s.(Server.OperationsPerformed) in
      let S2C_Client_VersionVector : (list u64) := s.(Server.VectorClock) in
      let S2C_Client_Number : u64 := r.(Message.C2S_Client_Id) in
      let S2C_Server_Id : u64 := s.(Server.Id) in
      (true, s, (Message.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 0 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number))
    else
      let v : nat := uint.nat (list_lookup_total (uint.nat s.(Server.Id)) s.(Server.VectorClock)) in
      let VectorClock : list u64 := <[(uint.nat s.(Server.Id))%nat := (W64 (v + 1))]>s.(Server.VectorClock) in
      let OperationsPerformed : list Operation.t := s.(Server.OperationsPerformed) ++ [Operation.mk VectorClock r.(Message.C2S_Client_Data)] in
      let MyOperations : list Operation.t := s.(Server.MyOperations) ++ [Operation.mk VectorClock r.(Message.C2S_Client_Data)] in
      let S2C_Client_OperationType := 1 in
      let S2C_Client_Data := 0 in
      let S2C_Client_VersionVector := VectorClock in
      let S2C_Client_Number := r.(Message.C2S_Client_Id) in
      let S2C_Server_Id : u64 := s.(Server.Id) in
      (true, Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed MyOperations s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), (Message.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 1 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number)).

Definition coq_processRequest (s: Server.t) (r: Message.t) : (Server.t * list Message.t) :=
  match (uint.nat r.(Message.MessageType))%nat with
  | 0%nat =>
      let '(succeeded, server, reply) := coq_processClientRequest s r in
      if succeeded then
        (server, [reply])
      else
        let UnsatisfiedRequests := s.(Server.UnsatisfiedRequests) ++ [r] in 
        let server := Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements) in
        (server, [])
  | 1%nat =>
      let s := coq_receiveGossip s r in
      let outGoingRequests := [Message.mk 0 0 0 0 0 [] 0 0 [] 0 (s.(Server.Id)) (r.(Message.S2S_Gossip_Sending_ServerId)) (r.(Message.S2S_Gossip_Index)) 0 0 [] 0 0] in
      let '(_, deletedIndex, outGoingRequests) := fold_left (fun (acc: nat * list nat * list Message.t) element =>
                                           let '(index, deletedIndex, acc) := acc in
                                           let '(succeeded, server, reply) := coq_processClientRequest s r in
                                           if succeeded then
                                             ((index + 1)%nat, deletedIndex ++ [index], acc ++ [reply])
                                           else
                                             ((index + 1)%nat, deletedIndex, acc)) s.(Server.UnsatisfiedRequests) (0%nat, [], outGoingRequests) in
      let remainingIndexes := list_difference (seq 0 (length s.(Server.UnsatisfiedRequests))) deletedIndex in 
      let UnsatisfiedRequests := 
        fold_left (fun acc index =>
                     match (s.(Server.UnsatisfiedRequests) !! index) with
                     | Some v => acc ++ [v]
                     | None => acc
                     end
          ) remainingIndexes [] in
      let s := Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements) in
      (s, outGoingRequests)
  | 2%nat =>
      let s := coq_acknowledgeGossip s r in
      (s, [])
  | 3%nat =>
      let outGoingRequests := fold_left (fun acc (index: nat) =>
                                           if (negb (index =? (uint.nat s.(Server.Id)))) then
                                             let S2S_Gossip_Sending_ServerId := s.(Server.Id) in
                                              let S2S_Gossip_Receiving_ServerId := index in
                                              let S2S_Gossip_Operations := coq_getGossipOperations s index in
                                              let S2S_Gossip_Index := length (s.(Server.MyOperations)) in
                                              let message := Message.mk 1 0 0 0 0 [] S2S_Gossip_Sending_ServerId S2S_Gossip_Receiving_ServerId S2S_Gossip_Operations S2S_Gossip_Index 0 0 0 0 0 [] 0 0 in acc ++ [message]
                                            else
                                              acc) (seq 0 (uint.nat s.(Server.NumberOfServers)))  [] in
      (s, outGoingRequests)
        
  | _ => (s, [])
  end.

Section heap.

  Context `{hG: !heapGS Σ}.

  Lemma wp_processClientRequest sv s msgv msg (n: nat) len_vc len_op len_mo len_po len_ga c2s s2c :
    {{{
        is_server sv s n len_vc len_op len_mo len_po len_ga ∗ 
        is_message msgv msg n c2s s2c
    }}}
      processClientRequest (server_val sv) (message_val msgv)
    {{{ (b: bool) ns nm, RET (#b, server_val ns, message_val nm);
        is_server ns (coq_processClientRequest s msg).1.2 n len_vc len_op len_mo len_po len_ga ∗
        is_message nm (coq_processClientRequest s msg).2 n c2s s2c  ∗
        ⌜b = (coq_processClientRequest s msg).1.1⌝
    }}}.
  Proof.
    iIntros "%Φ (H_is_server & H_is_message) HΦ".
  Admitted.

(*
  Lemma wp_processRequest
*)

End heap.
