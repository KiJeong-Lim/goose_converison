From Perennial.program_proof.session Require Export session_prelude.
From Perennial.program_proof.session Require Export coq_session.
From Perennial.program_proof.session Require Export versionVector.


Section heap.
  Context `{hG: !heapGS Σ}.

  Lemma wp_processClientRequest (sv: u64*u64*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t*Slice.t) (s: Server.t)
    (msgv: u64*u64*u64*u64*u64*Slice.t*u64*u64*Slice.t*u64*u64*u64*u64*u64*u64*Slice.t*u64*u64) (msg: Message.t) (n: nat) :
    {{{
          is_server sv s n ∗ 
          is_message msgv msg n
    }}}
      processClientRequest (server_val sv) (message_val msgv)
      {{{
            b ns nm , RET (b, server_val ns, message_val nm);
            is_server ns (coq_processClientRequest s msg).1.2 n ∗
            is_message nm (coq_processClientRequest s msg).2 n ∗
            ⌜b = #(coq_processClientRequest s msg).1.1⌝
      }}}.
  Proof.
    iIntros "%Φ (H1 & H2) H_ret".
    iDestruct "H1" as "(%H1 & %H2 & H1 & %H3 & H4 & H5 & H6 & H7 & %H4 & H8)".
    iDestruct "H2" as "(%H5 & %H6 & %H7 & %H8 & %H9 & %H10 & H9 & %H11 & %H12 & H10 & %H13 & %H14 & %H15 & %H16 & %H17 & %H18 & %H19 & H11 & %H20 & %H21)".
    rewrite /processClientRequest. wp_pures.
    wp_apply (wp_ref_to); first repeat apply (@val_ty_pair); auto.
    iIntros (ret) "H2".
    wp_apply (wp_compareVersionVector with "[H4 H9]"). { iFrame.
                                                         iPureIntro.
                                                         rewrite <- H3.
                                                         rewrite <- H10.
                                                         auto. }
    iIntros (r) "(%H22 & H12 & H13 & %H23)".
    wp_if_destruct.
    - wp_pures. wp_load. 
      assert (zero_val uint64T = #(@W64 0)) by auto. 
      assert (zero_val (slice.T uint64T) = slice_val Slice.nil) by auto.
      assert (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht))
              = slice_val Slice.nil) by auto.
      rewrite H H0 H3. unfold message_val.
      assert (message_val ((W64 0),
       (W64 0),
        (W64 0),
         (W64 0),
          (W64 0),
           Slice.nil,
            (W64 0),
             (W64 0),
              Slice.nil,
               (W64 0),
                (W64 0),
                 (W64 0),
                  (W64 0),
                   (W64 0),
                    (W64 0), Slice.nil, (W64 0), (W64 0)) = (#(W64 0),
       (#(W64 0),
        (#(W64 0),
         (#(W64 0),
          (#(W64 0),
           (Slice.nil,
            (#(W64 0),
             (#(W64 0),
              (Slice.nil,
               (#(W64 0),
                (#(W64 0),
                 (#(W64 0),
                  (#(W64 0),
                   (#(W64 0),
                    (#(W64 0), (Slice.nil, (#(W64 0), (#(W64 0), #()))))))))))))))))))%V). { unfold message_val. simpl. auto. }
      wp_pures.
      iModIntro.
      rewrite <- H22.
      iApply "H_ret".
                                 ).
      
      (* I'm not sure why we can't apply H_ret *)
  Admitted.
      
    
    
End heap.
