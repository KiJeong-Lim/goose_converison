From Perennial.program_proof.session Require Export coq_session coq_session_client.

Reserved Infix "=~=" (at level 70, no associativity).

Class Similarity (A : Type) (A' : Type) : Type :=
  is_similar_to (x : A) (x' : A') : Prop.

Infix "=~=" := is_similar_to.

(** Section BasicInstances_of_Similarity. *)

#[global]
Instance Similarity_forall {D : Type} {D' : Type} {C : D -> Type} {C' : D' -> Type} (DOM_SIM : Similarity D D') (COD_SIM : forall x : D, forall x' : D', x =~= x' -> Similarity (C x) (C' x')) : Similarity (forall x : D, C x) (forall x' : D', C' x') :=
  fun f => fun f' => forall x : D, forall x' : D', forall x_corres : x =~= x', @is_similar_to (C x) (C' x') (COD_SIM x x' x_corres) (f x) (f' x').

Lemma Similarity_fun_unfold {D : Type} {D' : Type} {C : Type} {C' : Type} {DOM_SIM : Similarity D D'} {COD_SIM : Similarity C C'} (f : D -> C) (f' : D' -> C')
  : (f =~= f') = (forall x : D, forall x' : D', forall x_corres : x =~= x', f x =~= f' x').
Proof.
  reflexivity.
Defined.

#[global]
Instance Similarity_sig {A : Type} {A' : Type} {P : A -> Prop} {P' : A' -> Prop} (SIM : Similarity A A') : Similarity { x : A | P x } { x' : A' | P' x' } :=
  fun s => fun s' => proj1_sig s =~= proj1_sig s'.

#[global]
Instance Similarity_prod {A : Type} {A' : Type} {B : Type} {B' : Type} (FST_SIM : Similarity A A') (SND_SIM : Similarity B B') : Similarity (A * B) (A' * B') :=
  fun p => fun p' => fst p =~= fst p' /\ snd p =~= snd p'.

Inductive list_corres {A : Type} {A' : Type} {SIM : Similarity A A'} : Similarity (list A) (list A') :=
  | nil_corres
    : [] =~= []
  | cons_corres (x : A) (x' : A') (xs : list A) (xs' : list A')
    (head_corres : x =~= x')
    (tail_corres : xs =~= xs')
    : x :: xs =~= x' :: xs'.

#[local] Hint Constructors list_corres : core.

#[global]
Instance Similarity_list {A : Type} {A' : Type} (SIM : Similarity A A') : Similarity (list A) (list A') :=
  @list_corres A A' SIM.

Inductive option_corres {A : Type} {A' : Type} {SIM : Similarity A A'} : Similarity (option A) (option A') :=
  | None_corres
    : None =~= None
  | Some_corres (x : A) (x' : A')
    (x_corres : x =~= x')
    : Some x =~= Some x'.

#[local] Hint Constructors option_corres : core.

#[global]
Instance Similarity_option {A : Type} {A' : Type} (SIM : Similarity A A') : Similarity (option A) (option A') :=
  @option_corres A A' SIM.

#[global]
Instance Similarity_bool : Similarity bool bool :=
  @eq bool.

#[global]
Instance Similarity_nat : Similarity nat nat :=
  @eq nat.

(** End BasicInstances_of_Similarity. *)

#[global]
Instance Similarity_u64 : Similarity u64 nat :=
  fun n => fun n' => (uint.nat n = n')%nat /\ (uint.Z n >= 0 /\ uint.Z n <= CONSTANT)%Z.

Lemma Similarity_u64_range (n : u64) (n' : nat)
  (n_corres : n =~= n')
  : (uint.Z n >= 0 /\ uint.Z n <= CONSTANT)%Z.
Proof.
  do 2 red in n_corres. word.
Qed.

Lemma list_corres_length {A : Type} {A' : Type} {SIM : Similarity A A'} (xs : list A) (xs' : list A')
  (xs_corres : xs =~= xs')
  : @length A xs = @length A' xs'.
Proof.
  induction xs_corres; simpl; congruence.
Qed.

Lemma last_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (xs : list A) (xs' : list A')
  (xs_corres : xs =~= xs')
  : @last A xs =~= @last A' xs'.
Proof.
  induction xs_corres as [ | ? ? ? ? ? [ | ? ? ? ? ? ?] ?]; simpl; eauto.
Qed.

Lemma app_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (xs : list A) (xs' : list A') (ys : list A) (ys' : list A')
  (xs_corres : xs =~= xs')
  (ys_corres : ys =~= ys')
  : @app A xs ys =~= @app A' xs' ys'.
Proof.
  revert ys ys' ys_corres; induction xs_corres; simpl; eauto.
Qed.

Lemma fold_left_corres {A : Type} {A' : Type} {B : Type} {B' : Type} {A_SIM : Similarity A A'} {B_SIM : Similarity B B'} (f : A -> B -> A) (xs : list B) (z : A) (f' : A' -> B' -> A') (xs' : list B') (z' : A')
  (f_corres : f =~= f')
  (xs_corres : xs =~= xs')
  (z_corres : z =~= z')
  : @fold_left A B f xs z =~= @fold_left A' B' f' xs' z'.
Proof.
  do 4 red in f_corres; revert z z' z_corres; induction xs_corres; simpl; eauto.
Qed.

Lemma fold_left_corres_withInvariant {A : Type} {A' : Type} {B : Type} {B' : Type} {A_SIM : Similarity A A'} {B_SIM : Similarity B B'} (Φ : forall ACCUM : A, forall ACCUM' : A', forall NEXTS : list B, forall NEXTS' : list B', Prop) (f : A -> B -> A) (f' : A' -> B' -> A') (xs : list B) (xs' : list B') (z : A) (z' : A')
  (f_corres : forall x : B, forall x' : B', x =~= x' -> forall z : A, forall z' : A', z =~= z' -> forall xs : list B, forall xs' : list B', Φ z z' (x :: xs) (x' :: xs') -> f z x =~= f' z' x')
  (xs_corres : xs =~= xs')
  (z_corres : z =~= z')
  (STEP : forall x : B, forall x' : B', x =~= x' -> forall z : A, forall z' : A', z =~= z' -> forall xs : list B, forall xs' : list B', Φ z z' (x :: xs) (x' :: xs') -> Φ (f z x) (f' z' x') xs xs')
  (INIT : Φ z z' xs xs')
  : fold_left f xs z =~= fold_left f' xs' z' /\ Φ (fold_left f xs z) (fold_left f' xs' z') [] [].
Proof.
  revert z z' z_corres INIT; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; simpl; intros; [eauto | eapply IH; eauto; eapply f_corres; eauto].
Qed.

Lemma take_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (n : nat) (n' : nat) (xs : list A) (xs' : list A')
  (n_corres : n =~= n')
  (xs_corres : xs =~= xs')
  : @take A n xs =~= @take A' n' xs'.
Proof.
  do 2 red in n_corres; subst n'; revert xs xs' xs_corres; induction n as [ | n IH]; intros ? ? xs_corres; destruct xs_corres as [ | x x' x_corres xs xs' xs_corres]; simpl in *; eauto.
Qed.

Lemma drop_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (n : nat) (n' : nat) (xs : list A) (xs' : list A')
  (n_corres : n =~= n')
  (xs_corres : xs =~= xs')
  : @drop A n xs =~= @drop A' n' xs'.
Proof.
  do 2 red in n_corres; subst n'; revert xs xs' xs_corres; induction n as [ | n IH]; intros ? ? xs_corres; destruct xs_corres as [ | x x' x_corres xs xs' xs_corres]; simpl in *; eauto.
Qed.

Lemma andb_corres (b1 : bool) (b1' : bool) (b2 : bool) (b2' : bool)
  (b1_corres : b1 =~= b1')
  (b2_corres : b2 =~= b2')
  : b1 && b2 =~= b1' && b2'.
Proof.
  do 2 red in b1_corres, b2_corres |- *; congruence.
Qed.

Lemma orb_corres (b1 : bool) (b1' : bool) (b2 : bool) (b2' : bool)
  (b1_corres : b1 =~= b1')
  (b2_corres : b2 =~= b2')
  : b1 || b2 =~= b1' || b2'.
Proof.
  do 2 red in b1_corres, b2_corres |- *; congruence.
Qed.

Lemma negb_corres (b1 : bool) (b1' : bool)
  (b1_corres : b1 =~= b1')
  : negb b1 =~= negb b1'.
Proof.
  do 2 red in b1_corres |- *; congruence.
Qed.

Lemma ite_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (b : bool) (b' : bool) (x : A) (x' : A') (y : A) (y' : A')
  (b_corres : b =~= b')
  (x_corres : x =~= x')
  (y_corres : y =~= y')
  : (if b then x else y) =~= (if b' then x' else y').
Proof.
  do 2 red in b_corres; destruct b as [ | ]; subst b'; simpl; eauto.
Qed.

Lemma ite_corres_op {A : Type} {A' : Type} {A_SIM : Similarity A A'} (b : bool) (b' : bool) (x : A) (x' : A') (y : A) (y' : A')
  (b_corres : negb b =~= b')
  (x_corres : x =~= x')
  (y_corres : y =~= y')
  : (if b then x else y) =~= (if b' then y' else x').
Proof.
  do 2 red in b_corres; destruct b as [ | ]; subst b'; simpl in *; eauto.
Qed.

Lemma match_option_corres {A : Type} {A' : Type} {B : Type} {B' : Type} {A_SIM : Similarity A A'} {B_SIM : Similarity B B'} (x : option A) (x' : option A') (f : A -> B) (f' : A' -> B') (z : B) (z' : B')
  (x_corres : x =~= x')
  (f_corres : f =~= f')
  (z_corres : z =~= z')
  : (match x with Some y => f y | None => z end) =~= (match x' with Some y' => f' y' | None => z' end).
Proof.
  destruct x_corres; eauto.
Qed.

Lemma fst_corres {A : Type} {A' : Type} {B : Type} {B' : Type} {A_SIM : Similarity A A'} {B_SIM : Similarity B B'} (p : A * B) (p' : A' * B')
  (p_corres : p =~= p')
  : @fst A B p =~= @fst A' B' p'.
Proof.
  destruct p_corres as [? ?]; eauto.
Qed.

Lemma snd_corres {A : Type} {A' : Type} {B : Type} {B' : Type} {A_SIM : Similarity A A'} {B_SIM : Similarity B B'} (p : A * B) (p' : A' * B')
  (p_corres : p =~= p')
  : @snd A B p =~= @snd A' B' p'.
Proof.
  destruct p_corres as [? ?]; eauto.
Qed.

Lemma list_lookup_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (xs : list A) (xs' : list A') (n : nat) (n' : nat)
  (xs_corres : xs =~= xs')
  (n_corres : n =~= n')
  : xs !! n =~= xs' !! n'.
Proof.
  do 2 red in n_corres; subst n'; revert n; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; destruct n as [ | n']; simpl in *; eauto.
Qed.

Lemma list_update_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (n : nat) (n' : nat) (y : A) (y' : A') (xs : list A) (xs' : list A')
  (n_corres : n =~= n')
  (y_corres : y =~= y')
  (xs_corres : xs =~= xs')
  : <[n:=y]> xs =~= <[n':=y']> xs'.
Proof.
  do 2 red in n_corres; subst n'; revert n y y' y_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; destruct n as [ | n']; intros; simpl; eauto.
Qed.

Lemma replicate_corres {A : Type} {A' : Type} {A_SIM : Similarity A A'} (n : nat) (n' : nat) (x : A) (x' : A')
  (n_corres : n =~= n')
  (x_corres : x =~= x')
  : replicate n x =~= replicate n' x'.
Proof.
  do 2 red in n_corres; subst n'; induction n as [ | n IH]; simpl; eauto.
Qed.

Lemma seq_0_corres (n : u64) (n' : nat)
  (n_corres : n =~= n')
  : map (λ i : nat, W64 i) (seq 0 n') =~= seq 0 n'.
Proof.
  do 2 red in n_corres. destruct n_corres as [EQ [LE GE]].
  revert n EQ LE GE. induction n' as [ | n' IH]; intros; eauto.
  rewrite -> seq_S in *. rewrite -> map_app in *. simpl in *.
  eapply app_corres.
  - eapply IH with (n := W64 n'); eauto; try word.
  - econstructor 2; eauto. do 2 red; word.
Qed.

Lemma eqb_0_corres (n : u64) (n' : nat)
  (n_corres : n =~= n')
  : (uint.Z n =? 0)%Z =~= (n' =? 0)%nat.
Proof.
  do 2 red in n_corres |- *. (destruct (uint.Z n =? 0)%Z as [ | ] eqn: H_OBS; [rewrite Z.eqb_eq in H_OBS | rewrite Z.eqb_neq in H_OBS]); (destruct (n' =? 0)%nat as [ | ] eqn: H_OBS'; [rewrite Nat.eqb_eq in H_OBS' | rewrite Nat.eqb_neq in H_OBS']); word.
Qed.

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

#[local] Hint Constructors Operation'.corres : core.

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

#[local] Hint Constructors Message'.corres : core.

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

  Record corres (s : Server.t) (s' : Server'.t) : Prop :=
    Similarity_Server_INTRO
    { Id_corres : s.(Server.Id) =~= s'.(Id)
    ; NumberOfServers_corres : s.(Server.NumberOfServers) =~= s'.(NumberOfServers)
    ; UnsatisfiedRequests_corres : s.(Server.UnsatisfiedRequests) =~= s'.(UnsatisfiedRequests)
    ; VectorClock_corres : s.(Server.VectorClock) =~= s'.(VectorClock)
    ; OperationsPerformed_corres : s.(Server.OperationsPerformed) =~= s'.(OperationsPerformed)
    ; MyOperations_corres : s.(Server.MyOperations) =~= s'.(MyOperations)
    ; PendingOperations_corres : s.(Server.PendingOperations) =~= s'.(PendingOperations)
    ; GossipAcknowledgements_corres : s.(Server.GossipAcknowledgements) =~= s'.(GossipAcknowledgements)
    }.

End Server'.

#[local] Hint Constructors Server'.corres : core.

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

  Record corres (c : Client.t) (c' : Client'.t) : Prop :=
    Similarity_Client_INTRO
    { Id_corres : c.(Client.Id) =~= c'.(Id)
    ; NumberOfServers_corres : c.(Client.NumberOfServers) =~= c'.(NumberOfServers)
    ; WriteVersionVector_corres : c.(Client.WriteVersionVector) =~= c'.(WriteVersionVector)
    ; ReadVersionVector_corres : c.(Client.ReadVersionVector) =~= c'.(ReadVersionVector)
    ; SessionSemantic_corres : c.(Client.SessionSemantic) =~= c'.(SessionSemantic)
    }.

End Client'.

#[local] Hint Constructors Client'.corres : core.

#[global]
Instance Similarity_Client : Similarity Client.t Client'.t :=
  Client'.corres.

(*
Module NatImplServer.

  Fixpoint coq_compareVersionVector (v1 : list nat) (v2 : list nat) : bool :=
    match v1 with
    | [] => true
    | h1 :: t1 =>
      match v2 with
      | [] => true
      | h2 :: t2 => (h2 <=? h1)%nat && coq_compareVersionVector t1 t2
      end
    end.

  Fixpoint coq_lexicographicCompare (v1 : list nat) (v2 : list nat) : bool :=
    match v1 with
    | [] => false 
    | h1 :: t1 =>
      match v2 with
      | [] => false 
      | h2 :: t2 => if (h1 =? h2)%nat then coq_lexicographicCompare t1 t2 else (h2 <? h1)%nat
      end
    end.

  Definition coq_maxTwoInts (x : nat) (y : nat) : nat :=
    if (y <? x)%nat then x else y.

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
      if canApply && (e1 + 1 =? e2)%nat then (output, false) else ((e2 <=? e1)%nat && output, canApply)
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
    | h :: t => if coq_lexicographicCompare h.(Operation'.VersionVector) i.(Operation'.VersionVector) || coq_equalSlices h.(Operation'.VersionVector) i.(Operation'.VersionVector) then i :: h :: t else h :: coq_sortedInsert t i
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
    take index o ++ drop (index + 1)%nat o.

  Definition coq_deleteAtIndexMessage (m : list Message'.t) (index : nat) : list Message'.t :=
    take index m ++ drop (index + 1)%nat m.

  Definition coq_getDataFromOperationLog (l : list Operation'.t) : nat :=
    match last l with
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
    if (i <? length l)%nat then
      let prevGossipAcknowledgementsValue : nat :=
        match s.(Server'.GossipAcknowledgements) !! i with
        | Some x => x
        | None => 0%nat
        end
      in
      let newGossipAcknowledgements := coq_maxTwoInts prevGossipAcknowledgementsValue r.(Message'.S2S_Acknowledge_Gossip_Index) in
      let gossipAcknowledgements := <[i := newGossipAcknowledgements]> l in
      Server'.mk s.(Server'.Id) s.(Server'.NumberOfServers) s.(Server'.UnsatisfiedRequests) s.(Server'.VectorClock) s.(Server'.OperationsPerformed) s.(Server'.MyOperations) s.(Server'.PendingOperations) gossipAcknowledgements
    else
      s.

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
        (true, s, Message'.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 0 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number)
      else
        let v : nat :=
          match s.(Server'.VectorClock) !! s.(Server'.Id) with
          | Some v => v
          | None => 0%nat
          end
        in
        let VectorClock := <[s.(Server'.Id) := (v + 1)%nat]> s.(Server'.VectorClock) in
        let OperationsPerformed := coq_sortedInsert s.(Server'.OperationsPerformed) (Operation'.mk VectorClock r.(Message'.C2S_Client_Data)) in
        let MyOperations := coq_sortedInsert s.(Server'.MyOperations) (Operation'.mk VectorClock r.(Message'.C2S_Client_Data)) in
        let S2C_Client_OperationType := 1%nat in
        let S2C_Client_Data := 0%nat in
        let S2C_Client_VersionVector := VectorClock in
        let S2C_Client_Number := r.(Message'.C2S_Client_Id) in
        let S2C_Server_Id := s.(Server'.Id) in
        (true, Server'.mk s.(Server'.Id) s.(Server'.NumberOfServers) s.(Server'.UnsatisfiedRequests) VectorClock OperationsPerformed MyOperations s.(Server'.PendingOperations) s.(Server'.GossipAcknowledgements), Message'.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 1 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number).

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
      (server, fold_left loop_step (seq 0%nat server.(Server'.NumberOfServers)) loop_init)
    | _ => (server, [])
    end.

  Lemma coq_compareVersionVector_corres
    : CoqSessionServer.coq_compareVersionVector =~= coq_compareVersionVector.
  Proof.
    intros xs xs' xs_corres ys ys' ys_corres; revert ys ys' ys_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl; try now red; reflexivity.
    do 2 red in x_corres, y_corres. destruct x_corres as [<- [? ?]], y_corres as [<- [? ?]]; (destruct (uint.nat x <? uint.nat y)%Z as [ | ] eqn: H_OBS; [rewrite Z.ltb_lt in H_OBS | rewrite Z.ltb_ge in H_OBS]); (destruct (uint.nat y <=? uint.nat x)%nat as [ | ] eqn: H_OBS'; [rewrite Nat.leb_le in H_OBS' | rewrite Nat.leb_gt in H_OBS']); simpl in *; eauto with *.
  Qed.

  #[global] Hint Resolve coq_compareVersionVector_corres : session_hints.

  Lemma coq_lexicographicCompare_corres
    : CoqSessionServer.coq_lexicographicCompare =~= coq_lexicographicCompare.
  Proof.
    intros xs xs' xs_corres ys ys' ys_corres; revert ys ys' ys_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl; try now red; reflexivity.
    do 2 red in x_corres, y_corres. destruct x_corres as [<- [? ?]], y_corres as [<- [? ?]]; (destruct (uint.Z x =? uint.Z y)%Z as [ | ] eqn: H_OBS; [rewrite Z.eqb_eq in H_OBS | rewrite Z.eqb_neq in H_OBS]); (destruct (uint.nat x =? uint.nat y)%nat as [ | ] eqn: H_OBS'; [rewrite Nat.eqb_eq in H_OBS' | rewrite Nat.eqb_neq in H_OBS']); simpl in *.
    - eauto with *.
    - word.
    - word.
    - do 2 red. rewrite Z.gtb_ltb. destruct (uint.nat y <? uint.nat x)%nat as [ | ] eqn: H_OBS1; [rewrite Nat.ltb_lt in H_OBS1 | rewrite Nat.ltb_ge in H_OBS1].
      + rewrite Z.ltb_lt. word.
      + rewrite Z.ltb_ge. word.
  Qed.

  #[global] Hint Resolve coq_lexicographicCompare_corres : session_hints.

  Lemma coq_maxTwoInts_corres
    : CoqSessionServer.coq_maxTwoInts =~= coq_maxTwoInts.
  Proof.
    intros x x' x_corres y y' y_corres; unfold CoqSessionServer.coq_maxTwoInts, coq_maxTwoInts.
    do 2 red in x_corres, y_corres. destruct x_corres as [<- [? ?]], y_corres as [<- [? ?]].
    rewrite Z.gtb_ltb; (destruct (uint.Z y <? uint.Z x)%Z as [ | ] eqn: H_OBS; [rewrite Z.ltb_lt in H_OBS | rewrite Z.ltb_ge in H_OBS]); (destruct (uint.nat y <? uint.nat x)%nat as [ | ] eqn: H_OBS'; [rewrite Nat.ltb_lt in H_OBS' | rewrite Nat.ltb_nlt in H_OBS']); (do 2 red; try word).
  Qed.

  #[global] Hint Resolve coq_maxTwoInts_corres : session_hints.

  Lemma coq_maxTS_corres
    : CoqSessionServer.coq_maxTS =~= coq_maxTS.
  Proof.
    intros xs xs' xs_corres ys ys' ys_corres; revert ys ys' ys_corres.
    induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl; eauto.
    econstructor 2; eauto. eapply coq_maxTwoInts_corres; eauto with *.
  Qed.

  #[global] Hint Resolve coq_maxTS_corres : session_hints.

  Lemma coq_oneOffVersionVector_corres
    : CoqSessionServer.coq_oneOffVersionVector =~= coq_oneOffVersionVector.
  Proof.
    intros xs xs' xs_corres ys ys' ys_corres; unfold CoqSessionServer.coq_oneOffVersionVector, coq_oneOffVersionVector; do 2 red.
    destruct (fold_left _ _ _) as [output canApply] eqn: H_OBS in |- *.
    destruct (fold_left _ _ _) as [output' canApply'] eqn: H_OBS' in |- *.
    enough (want : (output, canApply) =~= (output', canApply')).
    { do 2 red in want. destruct want as [output_corres canApply_corres]; do 2 red in output_corres, canApply_corres; simpl in *. congruence. }
    rewrite <- H_OBS, <- H_OBS'. eapply fold_left_corres.
    - clear. intros acc acc' acc_corres element element' element_corres.
      do 2 red in acc_corres, element_corres. destruct acc as [output canApply], acc' as [output' canApply'].
      destruct acc_corres as [output_corres canApply_corres]; simpl in *. destruct element as [e1 e2], element' as [e1' e2'].
      destruct element_corres as [e1_corres e2_corres]; simpl in *. do 2 red in output_corres, canApply_corres, e1_corres, e2_corres.
      destruct e1_corres as [<- [? ?]], e2_corres as [<- [? ?]]; (destruct canApply as [ | ]; subst canApply'; simpl in * ); (destruct output as [ | ]; subst output'); simpl in *.
      + (destruct (uint.Z (w64_word_instance .(word.add) e1 (W64 1)) =? uint.Z e2)%Z as [ | ] eqn: H_OBS; [rewrite Z.eqb_eq in H_OBS | rewrite Z.eqb_neq in H_OBS]); (destruct (uint.nat e1 + 1 =? uint.nat e2)%nat as [ | ] eqn: H_OBS'; [rewrite Nat.eqb_eq in H_OBS' | rewrite Nat.eqb_neq in H_OBS']).
        { eauto with *. }
        { contradiction H_OBS'. enough (uint.Z e1 + 1 = uint.Z e2)%Z by word. rewrite <- H_OBS. unfold CONSTANT in *. word. }
        { contradiction H_OBS. enough (uint.nat e1 + 1 = uint.nat e2)%nat by word. rewrite <- H_OBS'. unfold CONSTANT in *. word. }
        { rewrite Z.geb_leb; (destruct (uint.nat e2 <=? uint.nat e1)%nat as [ | ] eqn: H_OBS1; [rewrite Nat.leb_le in H_OBS1 | rewrite Nat.leb_gt in H_OBS1]); (destruct (uint.Z e2 <=? uint.Z e1)%Z as [ | ] eqn: H_OBS1'; [rewrite Z.leb_le in H_OBS1' | rewrite Z.leb_gt in H_OBS1']); eauto with *. }
      + (destruct (uint.Z (w64_word_instance .(word.add) e1 (W64 1)) =? uint.Z e2)%Z as [ | ] eqn: H_OBS; [rewrite Z.eqb_eq in H_OBS | rewrite Z.eqb_neq in H_OBS]); (destruct (uint.nat e1 + 1 =? uint.nat e2)%nat as [ | ] eqn: H_OBS'; [rewrite Nat.eqb_eq in H_OBS' | rewrite Nat.eqb_neq in H_OBS']).
        { econstructor; reflexivity. }
        { contradiction H_OBS'. enough (uint.Z e1 + 1 = uint.Z e2)%Z by word. rewrite <- H_OBS. unfold CONSTANT in *. word. }
        { contradiction H_OBS. enough (uint.nat e1 + 1 = uint.nat e2)%nat by word. rewrite <- H_OBS'. unfold CONSTANT in *. word. }
        { rewrite Z.geb_leb; (destruct (uint.nat e2 <=? uint.nat e1)%nat as [ | ] eqn: H_OBS1; [rewrite Nat.leb_le in H_OBS1 | rewrite Nat.leb_gt in H_OBS1]); (destruct (uint.Z e2 <=? uint.Z e1)%Z as [ | ] eqn: H_OBS1'; [rewrite Z.leb_le in H_OBS1' | rewrite Z.leb_gt in H_OBS1']); eauto with *. }
      + rewrite Z.geb_leb; (destruct (uint.Z e2 <=? uint.Z e1)%Z as [ | ] eqn: H_OBS1; [rewrite Z.leb_le in H_OBS1 | rewrite Z.leb_gt in H_OBS1]); (destruct (uint.nat e2 <=? uint.nat e1)%nat as [ | ] eqn: H_OBS1'; [rewrite Nat.leb_le in H_OBS1' | rewrite Nat.leb_gt in H_OBS1']); eauto with *.
      + rewrite Z.geb_leb; (destruct (uint.Z e2 <=? uint.Z e1)%Z as [ | ] eqn: H_OBS1; [rewrite Z.leb_le in H_OBS1 | rewrite Z.leb_gt in H_OBS1]); (destruct (uint.nat e2 <=? uint.nat e1)%nat as [ | ] eqn: H_OBS1'; [rewrite Nat.leb_le in H_OBS1' | rewrite Nat.leb_gt in H_OBS1']); eauto with *.
    - clear output output' canApply canApply' H_OBS H_OBS'. revert ys ys' ys_corres.
      induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl in *; eauto.
      econstructor 2; eauto with *.
    - eauto with *.
  Qed.

  #[global] Hint Resolve coq_oneOffVersionVector_corres : session_hints.

  Lemma coq_equalSlices_corres
    : CoqSessionServer.coq_equalSlices =~= coq_equalSlices.
  Proof.
    intros xs xs' xs_corres ys ys' ys_corres; revert ys ys' ys_corres; induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros ? ? ys_corres; destruct ys_corres as [ | y y' ys ys' y_corres ys_corres]; simpl; try reflexivity.
    destruct x_corres as [<- [? ?]], y_corres as [<- [? ?]]; simpl in *; (destruct (uint.Z x =? uint.Z y)%Z as [ | ] eqn: H_OBS; [rewrite Z.eqb_eq in H_OBS | rewrite Z.eqb_neq in H_OBS]); (destruct (uint.nat x =? uint.nat y)%nat as [ | ] eqn: H_OBS'; [rewrite Nat.eqb_eq in H_OBS' | rewrite Nat.eqb_neq in H_OBS']); simpl in *; eauto with *.
  Qed.

  #[global] Hint Resolve coq_equalSlices_corres : session_hints.

  Lemma coq_equalOperations_corres
    : CoqSessionServer.coq_equalOperations =~= coq_equalOperations.
  Proof.
    unfold CoqSessionServer.coq_equalOperations, coq_equalOperations. intros o1 o1' o1_corres o2 o2' o2_corres. destruct o1_corres, o2_corres. eapply andb_corres.
    - eapply coq_equalSlices_corres; eauto.
    - do 2 red in Data_corres, Data_corres0 |- *. destruct Data_corres as [? [? ?]], Data_corres0 as [? [? ?]]. rewrite -> H, -> H2.
      destruct (o1'.(Operation'.Data) =? o2'.(Operation'.Data))%nat as [ | ] eqn: H_OBS; [rewrite Nat.eqb_eq in H_OBS; rewrite Z.eqb_eq | rewrite Nat.eqb_neq in H_OBS; rewrite Z.eqb_neq]; word.
  Qed.

  #[global] Hint Resolve coq_equalOperations_corres : session_hints.

  Lemma coq_sortedInsert_corres
    : CoqSessionServer.coq_sortedInsert =~= coq_sortedInsert.
  Proof.
    intros xs xs' xs_corres y y' y_corres; revert y y' y_corres.
    induction xs_corres as [ | x x' xs xs' x_corres xs_corres IH]; intros; simpl; eauto.
    eapply ite_corres.
    - destruct x_corres, y_corres. eapply orb_corres.
      + eapply coq_lexicographicCompare_corres; eauto with *.
      + eapply coq_equalSlices_corres; eauto with *.
    - eauto.
    - eauto with *.
  Qed.

  #[global] Hint Resolve coq_sortedInsert_corres : session_hints.

  Lemma coq_mergeOperations_corres
    : CoqSessionServer.coq_mergeOperations =~= coq_mergeOperations.
  Proof.
    intros xs xs' xs_corres ys ys' ys_corres; unfold CoqSessionServer.coq_mergeOperations, coq_mergeOperations.
    eapply snd_corres. eapply fold_left_corres.
    - intros acc acc' acc_corres element element' element_corres.
      destruct acc as [index acc], acc' as [index' acc']; destruct acc_corres as [index_corres acc_corres]; simpl in *.
      eapply match_option_corres.
      + eapply list_lookup_corres.
        * eapply fold_left_corres; eauto with *.
        * do 2 red in index_corres |- *; word.
      + intros y y' y_corres. eapply ite_corres.
        * eapply coq_equalOperations_corres; eauto.
        * econstructor; simpl; eauto. do 2 red in index_corres |- *; word.
        * econstructor; simpl; eauto with *.
      + econstructor; simpl; eauto. 
        * eauto with *.
        * eapply app_corres; eauto with *.
    - eapply fold_left_corres; eauto with *.
    - eauto with *.
  Qed.

  #[global] Hint Resolve coq_mergeOperations_corres : session_hints.

  Lemma coq_deleteAtIndexOperation_corres
    : CoqSessionServer.coq_deleteAtIndexOperation =~= coq_deleteAtIndexOperation.
  Proof.
    intros xs xs' xs_corres n n' n_corres; unfold CoqSessionServer.coq_deleteAtIndexOperation, coq_deleteAtIndexOperation.
    eapply app_corres; [eapply take_corres | eapply drop_corres]; eauto; do 2 red in n_corres |- *; word.
  Qed.

  #[global] Hint Resolve coq_deleteAtIndexOperation_corres : session_hints.

  Lemma coq_deleteAtIndexMessage_corres
    : CoqSessionServer.coq_deleteAtIndexMessage =~= coq_deleteAtIndexMessage.
  Proof.
    intros xs xs' xs_corres n n' n_corres; unfold CoqSessionServer.coq_deleteAtIndexMessage, coq_deleteAtIndexMessage.
    eapply app_corres; [eapply take_corres | eapply drop_corres]; eauto; do 2 red in n_corres |- *; word.
  Qed.

  #[global] Hint Resolve coq_deleteAtIndexMessage_corres : session_hints.

  Lemma coq_getDataFromOperationLog_corres
    : CoqSessionServer.coq_getDataFromOperationLog =~= coq_getDataFromOperationLog.
  Proof.
    intros xs xs' xs_corres; unfold CoqSessionServer.coq_getDataFromOperationLog, coq_getDataFromOperationLog.
    eapply match_option_corres.
    - eapply last_corres; eauto.
    - intros x x' x_corres; destruct x_corres; eauto.
    - do 2 red; unfold CONSTANT; word.
  Qed.

  #[global] Hint Resolve coq_getDataFromOperationLog_corres : session_hints.

  Lemma coq_receiveGossip_corres
    : CoqSessionServer.coq_receiveGossip =~= coq_receiveGossip.
  Proof.
    intros s s' s_corres m m' m_corres; unfold CoqSessionServer.coq_receiveGossip, coq_receiveGossip.
    eapply ite_corres; trivial.
    { do 2 red. destruct m_corres; apply list_corres_length in S2S_Gossip_Operations_corres. destruct (length m'.(Message'.S2S_Gossip_Operations) =? 0)%nat as [ | ] eqn: H_OBS; [rewrite Nat.eqb_eq in H_OBS; rewrite Z.eqb_eq | rewrite Nat.eqb_neq in H_OBS; rewrite Z.eqb_neq]; word. }
    eapply snd_corres; eapply fold_left_corres.
    - intros acc acc' acc_corres e e' e_corres. destruct acc as [i s0], acc' as [i' s0']; destruct acc_corres as [i_corres s0_corres]; simpl in *. eapply ite_corres.
      + destruct s0_corres, e_corres; eapply coq_oneOffVersionVector_corres; trivial.
      + econstructor; simpl; trivial. destruct s0_corres, e_corres; econstructor; simpl; trivial.
        * eapply coq_maxTS_corres; eauto.
        * eapply coq_mergeOperations_corres; eauto. econstructor 2; econstructor; eauto.
        * eapply coq_deleteAtIndexOperation_corres; eauto.
      + econstructor; simpl; trivial. do 2 red in i_corres |- *; word.
    - destruct s_corres, m_corres; eapply coq_mergeOperations_corres; trivial.
    - econstructor; simpl.
      + reflexivity.
      + destruct s_corres; econstructor; simpl; trivial. destruct m_corres; eapply coq_mergeOperations_corres; trivial.
  Qed.

  #[global] Hint Resolve coq_receiveGossip_corres : session_hints.

  Lemma coq_acknowledgeGossip_corres
    : CoqSessionServer.coq_acknowledgeGossip =~= coq_acknowledgeGossip.
  Proof.
    intros s s' s_corres m m' m_corres; unfold CoqSessionServer.coq_acknowledgeGossip, coq_acknowledgeGossip.
    eapply ite_corres_dual; trivial.
    - do 2 red. symmetry. rewrite Z.geb_leb.
      destruct (length s .(Server.GossipAcknowledgements) <=? uint.Z m .(Message.S2S_Acknowledge_Gossip_Sending_ServerId)) as [ | ] eqn: H_OBS; [rewrite Z.leb_le in H_OBS | rewrite Z.leb_gt in H_OBS]; simpl.
      + rewrite Nat.ltb_ge. destruct s_corres, m_corres. do 2 red in S2S_Acknowledge_Gossip_Sending_ServerId_corres. apply list_corres_length in GossipAcknowledgements_corres. rewrite <- GossipAcknowledgements_corres. word.
      + rewrite Nat.ltb_lt. destruct s_corres, m_corres. do 2 red in S2S_Acknowledge_Gossip_Sending_ServerId_corres. apply list_corres_length in GossipAcknowledgements_corres. rewrite <- GossipAcknowledgements_corres. word.
    - destruct s_corres, m_corres; econstructor; simpl; trivial. eapply list_update_corres; trivial.
      + do 2 red in S2S_Acknowledge_Gossip_Sending_ServerId_corres |- *; word.
      + eapply coq_maxTwoInts_corres; trivial. eapply match_option_corres; trivial.
        * eapply list_lookup_corres; trivial. do 2 red in S2S_Acknowledge_Gossip_Sending_ServerId_corres |- *; word.
        * intros y y' y_corres. eauto.
        * do 2 red; unfold CONSTANT; word.
  Qed.

  #[global] Hint Resolve coq_acknowledgeGossip_corres : session_hints.

  Lemma coq_getGossipOperations_corres
    : CoqSessionServer.coq_getGossipOperations =~= coq_getGossipOperations.
  Proof.
    intros s s' s_corres i i' i_corres; unfold CoqSessionServer.coq_getGossipOperations, coq_getGossipOperations.
    eapply match_option_corres; eauto.
    - destruct s_corres; eapply list_lookup_corres; trivial. do 2 red in i_corres |- *; word.
    - intros y y' y_corres. destruct s_corres; eapply drop_corres; trivial. do 2 red in y_corres |- *; word.
  Qed.

  #[global] Hint Resolve coq_getGossipOperations_corres : session_hints.

  Lemma coq_processClientRequest_corres
    : CoqSessionServer.coq_processClientRequest =~= coq_processClientRequest.
  Proof.
    intros s s' s_corres m m' m_corres; unfold CoqSessionServer.coq_processClientRequest, coq_processClientRequest.
    eapply ite_corres; trivial.
    - eapply negb_corres. destruct s_corres, m_corres; eapply coq_compareVersionVector_corres; trivial.
    - econstructor; simpl.
      + econstructor; simpl; trivial. reflexivity.
      + econstructor; simpl; trivial; do 2 red; unfold CONSTANT; word.
    - eapply ite_corres.
      { destruct m_corres; do 2 red in C2S_Client_OperationType_corres |- *. destruct (m' .(Message'.C2S_Client_OperationType) =? 0)%nat as [ | ] eqn: H_OBS; [rewrite Nat.eqb_eq in H_OBS; rewrite Z.eqb_eq | rewrite Nat.eqb_neq in H_OBS; rewrite Z.eqb_neq]; word. }
      { econstructor; simpl.
        - econstructor; simpl; trivial. reflexivity.
        - destruct s_corres, m_corres; econstructor; simpl; trivial; try (do 2 red; unfold CONSTANT; word); trivial. eapply coq_getDataFromOperationLog_corres; trivial.
      }
      { assert (
          <[uint.nat (s .(Server.Id)):=W64 (match s .(Server.VectorClock) !! uint.nat s .(Server.Id) with Some v => uint.Z v | None => 0 end + 1)%Z]> s .(Server.VectorClock) =~= <[s' .(Server'.Id):=(match s' .(Server'.VectorClock) !! s' .(Server'.Id) with Some v => v | None => 0 end + 1)%nat]> s' .(Server'.VectorClock)
        ) as CLAIM.
        { destruct s_corres; eapply list_update_corres; simpl; trivial.
          - do 2 red in Id_corres |- *; word.
          - assert (s .(Server.VectorClock) !! uint.nat s .(Server.Id) =~= s' .(Server'.VectorClock) !! s' .(Server'.Id)) as YES1.
            { eapply list_lookup_corres; trivial. do 2 red in Id_corres |- *; word. }
            revert YES1. set (x := s .(Server.VectorClock) !! uint.nat s .(Server.Id)). set (x' := s' .(Server'.VectorClock) !! s' .(Server'.Id)).
            intros YES1. destruct YES1.
            + do 2 red; unfold CONSTANT; word.
            + do 2 red in x_corres |- *. admit.
        }
        econstructor; simpl.
        - econstructor; simpl.
          + reflexivity.
          + destruct s_corres, m_corres; econstructor; simpl; trivial; eapply coq_sortedInsert_corres; trivial; econstructor; simpl; trivial.
        - destruct s_corres, m_corres; econstructor; simpl; trivial; try (do 2 red; unfold CONSTANT; word); trivial.
      }
  Admitted.

  #[global] Hint Resolve coq_processClientRequest_corres : session_hints.

  Lemma coq_processRequest_corres
    : CoqSessionServer.coq_processRequest =~= coq_processRequest.
  Proof.
    intros s s' s_corres m m' m_corres; unfold CoqSessionServer.coq_processRequest, coq_processRequest.
    destruct s_corres, m_corres; do 2 red in MessageType_corres.
    destruct (uint.nat m.(Message.MessageType)) as [ | [ | [ | [ | n]]]] eqn: H_OBS; destruct (m'.(Message'.MessageType)) as [ | [ | [ | [ | n']]]] eqn: H_OBS'; try word.
    - assert (CoqSessionServer.coq_processClientRequest s m =~= coq_processClientRequest s' m') as YES1.
      { eapply coq_processClientRequest_corres; econstructor; simpl; trivial. do 2 red; word. }
      revert YES1. set (x := CoqSessionServer.coq_processClientRequest s m). set (x' := coq_processClientRequest s' m').
      intros YES1. destruct YES1 as [[x1_corres x2_corres] x3_corres]; simpl in *. destruct x as [[x1 x2] x3], x' as [[x1' x2'] x3']; simpl in *.
      eapply ite_corres; trivial.
      + econstructor; simpl; trivial. econstructor 2; eauto.
      + econstructor; simpl; eauto. destruct x2_corres, x3_corres; econstructor; simpl; trivial.
        eapply app_corres; eauto. econstructor 2; eauto. econstructor; simpl; trivial. do 2 red; word.
    - eapply snd_corres. eapply fold_left_corres.
      + intros acc acc' acc_corres element element' element_corres. destruct acc as [i [s0 outGoingRequests]], acc' as [i' [s0' outGoingRequests']]; simpl in *.
        destruct acc_corres as [i_corres [s0_corres outGoingRequests_corres]]; simpl in *.
        assert (CoqSessionServer.coq_processClientRequest s0 element =~= coq_processClientRequest s0' element') as YES1.
        { eapply coq_processClientRequest_corres; trivial. }
        revert YES1. set (x := CoqSessionServer.coq_processClientRequest s0 element). set (x' := coq_processClientRequest s0' element').
        intros YES1. destruct YES1 as [[x1_corres x2_corres] x3_corres]; simpl in *. destruct x as [[x1 x2] x3], x' as [[x1' x2'] x3']; simpl in *.
        eapply ite_corres; trivial.
        * econstructor; simpl; trivial. econstructor; simpl.
          { destruct x2_corres; econstructor; simpl; trivial. eapply coq_deleteAtIndexMessage_corres; trivial. }
          { eapply app_corres; trivial. econstructor 2; eauto. }
        * econstructor; simpl.
          { do 2 red in i_corres |- *; word. }
          { econstructor; simpl; trivial. }
      + assert (CoqSessionServer.coq_receiveGossip s m =~= coq_receiveGossip s' m') as YES1.
        { eapply coq_receiveGossip_corres; econstructor; simpl; trivial. do 2 red; word. }
        destruct YES1; trivial.
      + econstructor; simpl; try reflexivity. econstructor; simpl.
        * eapply coq_receiveGossip_corres; econstructor; simpl; trivial. do 2 red; word.
        * econstructor 2; eauto. econstructor; simpl; trivial; try (do 2 red; unfold CONSTANT; word); trivial.
        assert (CoqSessionServer.coq_receiveGossip s m =~= coq_receiveGossip s' m') as YES1.
        { eapply coq_receiveGossip_corres; econstructor; simpl; trivial. do 2 red; word. }
        destruct YES1; trivial.
    - econstructor; simpl; eauto. eapply coq_acknowledgeGossip_corres; econstructor; simpl; trivial. do 2 red; word.
    - econstructor; simpl.
      + econstructor; simpl; trivial.
      + eapply fold_left_corres.
        { intros acc acc' acc_corres index index' index_corres.
          eapply ite_corres; trivial.
          - eapply andb_corres.
            + eapply negb_corres. do 2 red in Id_corres, index_corres |- *. destruct (index' =? s' .(Server'.Id))%nat as [ | ] eqn: H_OBS1; [rewrite -> Nat.eqb_eq in H_OBS1 |- * | rewrite -> Nat.eqb_neq in H_OBS1 |- *]; word.
            + eapply negb_corres. do 2 red in index_corres |- *.
              assert (length (CoqSessionServer.coq_getGossipOperations s index) = length (coq_getGossipOperations s' index')) as CLAIM.
              { eapply list_corres_length. eapply coq_getGossipOperations_corres; [econstructor; simpl; trivial | do 2 red; word]. }
              rewrite CLAIM; trivial.
          - eapply app_corres; trivial. econstructor 2; eauto. econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
            + eapply coq_getGossipOperations_corres; trivial. econstructor; simpl; trivial.
            + admit.
        }
        { do 2 red in NumberOfServers_corres. destruct NumberOfServers_corres as (H & ? & ?). rewrite H.
          eapply seq_0_corres with (n := s.(Server.NumberOfServers)). econstructor; simpl; word.
        }
        { eauto. }
    - econstructor; simpl; eauto. econstructor; simpl; trivial.
  Admitted.

  #[global] Hint Resolve coq_processRequest_corres : session_hints.

End NatImplServer.

Export NatImplServer.

Module NatImplClient.

  Definition coq_read (c : Client'.t) (serverId : nat) : Message'.t :=
    match c.(Client'.SessionSemantic) with
    | 0%nat => Message'.mk 0 c.(Client'.Id) serverId 0 0 (replicate c.(Client'.NumberOfServers) 0%nat) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 1%nat => Message'.mk 0 c.(Client'.Id) serverId 0 0 (replicate c.(Client'.NumberOfServers) 0%nat) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 2%nat => Message'.mk 0 c.(Client'.Id) serverId 0 0 (replicate c.(Client'.NumberOfServers) 0%nat) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 3%nat => Message'.mk 0 c.(Client'.Id) serverId 0 0 c.(Client'.ReadVersionVector) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 4%nat => Message'.mk 0 c.(Client'.Id) serverId 0 0 c.(Client'.WriteVersionVector) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 5%nat => Message'.mk 0 c.(Client'.Id) serverId 0 0 (coq_maxTS c.(Client'.WriteVersionVector) c.(Client'.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | _ => Message'.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    end.

  Definition coq_write (c : Client'.t) (serverId : nat) (value : nat) : Message'.t :=
    match c.(Client'.SessionSemantic) with
    | 0%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value (replicate c.(Client'.NumberOfServers) 0%nat) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 1%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value c.(Client'.ReadVersionVector) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 2%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value c.(Client'.WriteVersionVector) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 3%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value (replicate c.(Client'.NumberOfServers) 0%nat) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 4%nat => Message'.mk 0 c.(Client'.Id) serverId 1 value (replicate c.(Client'.NumberOfServers) 0%nat) 0 0 [] 0 0 0 0 0 0 [] 0 0
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

  Lemma coq_read_corres
    : CoqSessionClient.coq_read =~= coq_read.
  Proof.
    intros c c' c_corres serverId serverId' serverId_corres; unfold CoqSessionClient.coq_read, coq_read.
    destruct c_corres; do 2 red in SessionSemantic_corres.
    destruct (uint.nat c .(Client.SessionSemantic)) as [ | [ | [ | [ | [ | [ | n]]]]]]; destruct (c' .(Client'.SessionSemantic)) as [ | [ | [ | [ | [ | [ | n']]]]]]; try word.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
      eapply replicate_corres; trivial.
      + do 2 red in NumberOfServers_corres |- *; word.
      + do 2 red; unfold CONSTANT; word.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
      eapply replicate_corres; trivial.
      + do 2 red in NumberOfServers_corres |- *; word.
      + do 2 red; unfold CONSTANT; word.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
      eapply replicate_corres; trivial.
      + do 2 red in NumberOfServers_corres |- *; word.
      + do 2 red; unfold CONSTANT; word.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
      eapply coq_maxTS_corres; trivial.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
  Qed.

  #[global] Hint Resolve coq_read_corres : session_hints.

  Lemma coq_write_corres
    : CoqSessionClient.coq_write =~= coq_write.
  Proof.
    intros c c' c_corres serverId serverId' serverId_corres value value' value_corres; unfold CoqSessionClient.coq_write, coq_write.
    destruct c_corres; do 2 red in SessionSemantic_corres.
    destruct (uint.nat c .(Client.SessionSemantic)) as [ | [ | [ | [ | [ | [ | n]]]]]]; destruct (c' .(Client'.SessionSemantic)) as [ | [ | [ | [ | [ | [ | n']]]]]]; try word.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
      eapply replicate_corres; trivial.
      + do 2 red in NumberOfServers_corres |- *; word.
      + do 2 red; unfold CONSTANT; word.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
      eapply replicate_corres; trivial.
      + do 2 red in NumberOfServers_corres |- *; word.
      + do 2 red; unfold CONSTANT; word.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
      eapply replicate_corres; trivial.
      + do 2 red in NumberOfServers_corres |- *; word.
      + do 2 red; unfold CONSTANT; word.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
      eapply coq_maxTS_corres; trivial.
    - econstructor; simpl; try (do 2 red; unfold CONSTANT; word); trivial.
  Qed.

  #[global] Hint Resolve coq_write_corres : session_hints.

  Lemma coq_processRequest_corres
    : CoqSessionClient.coq_processRequest =~= coq_processRequest.
  Proof.
    intros c c' c_corres requestType requestType' requestType_corres serverId serverId' serverId_corres value value' value_corres ackMessage ackMessage' ackMessage_corres.
    unfold CoqSessionClient.coq_processRequest, coq_processRequest. destruct c_corres, ackMessage_corres. do 2 red in requestType_corres.
    destruct (uint.nat requestType) as [ | [ | [ | n]]] eqn: H_OBS; destruct (requestType') as [ | [ | [ | n']]] eqn: H_OBS'; try word.
    - econstructor; simpl.
      + econstructor; simpl; trivial.
      + eapply coq_read_corres; trivial. econstructor; simpl; trivial.
    - econstructor; simpl.
      + econstructor; simpl; trivial.
      + eapply coq_write_corres; trivial. econstructor; simpl; trivial.
    - do 2 red in S2C_Client_OperationType_corres. destruct (uint.nat ackMessage .(Message.S2C_Client_OperationType)) as [ | [ | x]] eqn: H_OBS1; destruct (ackMessage' .(Message'.S2C_Client_OperationType)) as [ | [ | x']] eqn: H_OBS1'; try word.
      + econstructor; simpl; trivial; econstructor; simpl; trivial; do 2 red; unfold CONSTANT; word.
      + econstructor; simpl; trivial; econstructor; simpl; trivial; do 2 red; unfold CONSTANT; word.
      + econstructor; simpl; trivial; econstructor; simpl; trivial; do 2 red; unfold CONSTANT; word.
    - econstructor; simpl; trivial; econstructor; simpl; trivial; do 2 red; unfold CONSTANT; word.
  Qed.

  #[global] Hint Resolve coq_processRequest_corres : session_hints.

End NatImplClient.

Export NatImplClient.
*)
