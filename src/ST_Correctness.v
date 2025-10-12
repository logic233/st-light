From compcert Require Import cfrontend.ClightBigstep.
From compcert Require Import cfrontend.Clight.
From compcert Require Import cfrontend.Ctypes.
From compcert Require Import lib.Integers.
From compcert Require Import lib.Maps.
From compcert Require Import lib.Coqlib.
From compcert Require Errors.
From compcert Require Import common.Separation.
From compcert Require Import common.Values.
From compcert Require Import common.Memory.
From compcert Require Import common.Events.
From compcert Require Import common.Globalenvs.
From compcert Require Import common.Smallstep.
From compcert Require Import common.Behaviors.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import VelusMemory.
From Velus Require Import Ident.
From Velus Require Import Traces.

From Velus Require Import Common.CompCertLib.
From Velus Require Import ObcToClight.MoreSeparation.
Require Import ST_Invariant.
Require Import Cgen.
Require Import CgenProperties.
Require Import ST_Interface.

From Coq Require Import Program.Tactics.
From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import ZArith.BinInt.
From Coq Require Import Omega.
From Coq Require Import Sorting.Permutation.

Import ST.Typ.
Import ST.Syn.
Import ST.Sem.
Import OpAux.

Open Scope list_scope.
Open Scope sep_scope.
Open Scope Z.
Hint Constructors Clight.eval_lvalue Clight.eval_expr.
Hint Resolve  Clight.assign_loc_value.

Hint Resolve Z.divide_refl.
From Hammer Require Import Hammer Reconstr.

Section PRESERVATION.

  (*****************************************************************)
  (** we work in a well-typed translated program                  **)
  (*****************************************************************)

  Variable 
           (pro        : project)
           (tprog      : Clight.program).
  Let tge              := Clight.globalenv tprog.
  Let gcenv            := Clight.genv_cenv tge.

  Hypothesis (TRANSL : translate pro = Errors.OK tprog)
             (WT     : wt_project pro).
             
Lemma staterep_extract'': 
    forall    me b ofs m i c' po  P  pro_l'  pou_name d ty,
    find_pou pou_name pro = Some (po,pro_l') ->
    In (i,ty) ( po.(pou_vars)) ->
    get_pou_name ty = Some c' ->
    m |= staterep gcenv pro pou_name me b ofs ** P ->
    field_offset gcenv i (mk_members po) = Errors.OK d
    -> m |= staterep gcenv pro c' (instance_match i me) b (ofs + d)** P.
  Proof.
    intros.
    destruct ty;inv H1.

    eapply staterep_extract in WT as (? & WF & T); eauto.
    rewrite WF in H3.
    inv H3.
    eapply T.
    Qed.
  (* Opaque sepconj. *)


  (* Hint Resolve wt_val_load_result. *)
  (* Hint Constructors wt_stmt.  *)

  Section MatchStates.

    Variable
      (** ST POU *)
      (po_id  : ident) (po  : pou_decl)    

      (** ST state *)
      (me       : menv)      (ve     : venv)

      (** Clight state *)
      (m        : Mem.mem)   (e      : Clight.env) (le   : temp_env)

      (** Clight self structure *)
      (sb       : block)     (sofs   : ptrofs)


      (** frame *)
      (P        : massert).

    Hypothesis    
    (Findpou  : find_pou_decl po_id pro = Some po)
    (Hmem     : m |= match_states gcenv pro po  (me, ve) (e, le) sb sofs
                                  ** P).

    Section ExprCorrectness.

      (*****************************************************************)
      (** correctness of expressions                                  **)
      (*****************************************************************)


      Corollary eval_temp_var:
        forall x ty v,
          In (x, ty) (filter_val po.(pou_temps)  ) ->
          Env.find x ve = Some v ->
          eval_expr tge e le m (Etempvar x (cltype ty)) v.
      Proof.
        intros * Hvars Hx ; simpl.
        apply match_states_conj in Hmem as (Hmem &?).
        rewrite sep_swap in Hmem.
        apply sep_proj1,sep_pure' in Hmem.
        apply eval_Etempvar.
        apply in_map with (f:=fst) in Hvars;simpl in Hvars.
        eapply Forall_forall in Hmem;eauto.
        unfold match_var in Hmem; simpl in Hmem.
        cases; try contradiction.
        rewrite Hx in Hmem.
        simpl in Hmem. congruence.
      Qed.
   
   

      (** self->x and &self->o *)
      Section SelfField.

        Variable (x  : ident)
                 (ty : type).
        Let self_ind_field := deref_field self (pou_name po) x (cltype ty).

        Hypothesis (Hin : In (x, ty) ( po.(pou_vars)  ) /\ (is_inst ty) =false ).

        Lemma evall_self_field:
          exists d,
            eval_lvalue tge e le m self_ind_field sb (Ptrofs.add sofs (Ptrofs.repr d))
            /\ field_offset gcenv x (mk_members po) = Errors.OK d
            /\ 0 <= d <= Ptrofs.max_unsigned.
        Proof.
          apply match_states_conj in Hmem as (Hmem &?&?&?).
          pose proof (find_pou_name _ _ _  Findpou); subst.
          assert(A: exists pro',find_pou (pou_name po) pro =  Some (po, pro')).
          {
            eapply find_pou_decl2find_pou;eauto.
          }
          destruct A.
          edestruct make_members_co as (? & Hco & ? & Eq & ? & ?); eauto.
          destruct Hin as (Hin1 & Hin2).
          edestruct staterep_field_offset as (d & ? & ?); eauto.
          exists d; split; [|split]; auto.
          - eapply eval_Efield_struct; eauto.
            + eapply eval_Elvalue; eauto.
              now apply deref_loc_copy.
            + simpl; unfold type_of_inst; eauto.
            + now rewrite Eq.
          - split.
            + eapply field_offset_in_range'; eauto.
            + apply bounded_struct_of_class_ge0   in H. omega.
        Qed.

        Corollary eval_self_field:
          forall v,
            find_val x me = Some v ->
            eval_expr tge e le m self_ind_field v.
        Proof.
          intros.
          edestruct evall_self_field as (?&?&?&?); eauto.
          destruct Hin as (Hin1 & Hin2).
          apply match_states_conj in Hmem as (Hmem &?).
          eapply eval_Elvalue; eauto.
          erewrite find_pou_name in Hmem; eauto.
          eapply staterep_deref_mem; eauto.
          rewrite Ptrofs.unsigned_repr; auto.
        Qed.


      End SelfField.

      Section ExpField.
      (* Taking Invariants Ensure Semantic Consistency from the paper as an example, 
      this explains the fundamental approach of using theorem proving techniques to verify code generation correctness.*)
        
        (*1. introduce predefined types, including the source language ST-light and the target language Clight for code generation.*)
        (* expression for ST-light *)
        Print exp.
     

        (* expression for Clight *)
        Print expr.

        (* gen_exp is a fun from T-light to Clight*)
        Check gen_exp.
        Print gen_exp.

        (*2. let's prove *)

         Lemma evall_field :
          forall  ex env' po_nm'   po' l_idxs,
          wt_exp pro po ex ->
          exp_eval_me_idxs me ve ex l_idxs -> 
          me_idxs_get me l_idxs (Some env')->
          get_pou_name (typeof ex) = (Some po_nm') -> 
          find_pou_decl po_nm' pro = Some po' -> 
          exists d, m |= staterep gcenv  pro po_nm' env' sb (Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr d))) ** P /\
          bounded_struct_of_class gcenv po'  (Ptrofs.add sofs (Ptrofs.repr d)) /\ 
          eval_lvalue tge e le m (gen_exp po ex) sb  (Ptrofs.add sofs (Ptrofs.repr d)).
        Proof.
          induction ex;intros env' po_nm'   po' l_idxs
          WTE EVAL IDXS Name' Find' ; inv EVAL ;       simpl in Name'.
        
         eapply find_pou_decl2find_pou in Find';eauto.
        + (*Var i t*)
          inv WTE.     
          apply match_states_conj in Hmem as (Hmem &?&?&?).
          apply sep_drop2 in Hmem.
          pose proof (find_pou_name _ _ _  Findpou); subst.
          assert(A0: exists pro_l' : list pou_decl, find_pou (pou_name po) pro = Some (po, pro_l'))
            by ( apply find_pou_decl2find_pou in Findpou;eauto).
          destruct A0 as [l1 A0].
          assert(Findpou': exists pro',find_pou (pou_name po) pro =  Some (po, pro')).
          {
            eapply find_pou_decl2find_pou;eauto.
          }
          destruct Findpou' as [f1 ].
          edestruct make_members_co as (? & Hco & ? & Eq & ? & ?); eauto.
          edestruct staterep_field_offset2 with (1:=Findpou) as (? & ? & ?); eauto.
          eapply  staterep_extract'' in A0;  eauto.
          exists (x0) ;eauto.
          assert (A2: 0 <= Ptrofs.unsigned sofs + x0 <= Ptrofs.max_unsigned) by (eapply struct_in_bounds_field;eauto).
          assert(A3: Ptrofs.unsigned sofs + x0 =  
                      Ptrofs.unsigned  (Ptrofs.add sofs (Ptrofs.repr x0))
          ).
          {
          unfold Ptrofs.add.
          rewrite Ptrofs.unsigned_repr_eq.
          rewrite Ptrofs.unsigned_repr_eq.
          assert(M1:  0 <= Ptrofs.unsigned sofs + x0 <  Ptrofs.modulus ) by ( unfold Ptrofs.max_unsigned  in A2;omega 
          ).
          assert(M2: 0 <= x0) by ( eapply field_offset_in_range';eauto).
          assert(M3: 0 <= Ptrofs.unsigned sofs ) by (eapply Ptrofs.unsigned_range)  .
          rewrite (Z.mod_small x0 Ptrofs.modulus);auto.
          rewrite (Z.mod_small );eauto.
          omega.
          }        
          split.
            - 
              inv IDXS; try inv H10.
              rewrite <- A3.
              unfold instance_match  in A0.
              rewrite H12 in A0.
              apply A0.
              inv H11.
            - 
          split.
            --
            unfold bounded_struct_of_class.
            rewrite <-  A3.
            destruct Find' as [pro'].
            assert(Find': find_pou po_nm' pro = Some (po', pro')) by eauto.
            eapply make_members_co in Find' as [co [F00 [F01 [F02[F03 [F04]]]] ]]  ; eauto.
            rewrite <- F02.
            eapply struct_in_struct_in_bounds;eauto.
            eapply Consistent;eauto.
            eapply field_translate_obj_type;eauto.
            --
            simpl.
            eapply eval_Efield_struct; eauto.
            --- eapply eval_Elvalue; eauto.
              now apply deref_loc_copy.
            --- simpl; unfold type_of_inst; eauto.
            --- now rewrite Eq.
        + (*(Field ex i t)*)
          inv WTE. destruct (typeof ex) eqn:T_ex; inv H2.
          assert(Findpou' : find_pou_decl i0 pro = Some po0) by eauto.
          assert(Findpou'_ : find_pou_decl i0 pro = Some po0) by eauto.
          assert(A0: exists pro_l' : list pou_decl, find_pou i0 pro = Some (po0, pro_l')) by eauto.
          assert(A1: get_pou_name (Tinst i0) = Some i0) by eauto.
          assert (IN :  In (i, t) (filter_inst (pou_vars po0)) ) by auto.
          assert(A11 :  Clight.typeof (gen_exp po ex) = Tstruct i0 noattr  ) by ( rewrite type_pres; rewrite T_ex; eauto).
          destruct A0 as [l1 A0].
          inv IDXS.
          inv H4.
          eapply IHex with(2:= H4)(env':= me' ) in H6 as [x [IH1  [IH2 IH3] ]]; eauto.
          assert(Findpou'': exists pro',find_pou i0 pro =  Some (po0, pro')).
          {
            eapply find_pou_decl2find_pou;eauto.
          }
          destruct Findpou'' as [f1 ].
          eapply make_members_co in H  as (? & Hco & ? & Eq & ? & ?); eauto.
          eapply filter_val_filter_In2 in H3;eauto.
          assert(AA: In (i, t) (pou_vars po0)) by eauto.
          eapply c_objs_field_offset in H5; eauto.
          assert(Hoff: exists d,field_offset tge i ( mk_members po0) = Errors.OK d) by eauto .
          destruct Hoff as [x1 Hoff].
          eapply  staterep_extract'' in A0; eauto.
          unfold instance_match  in A0.
          rewrite H7  in A0.
          unfold bounded_struct_of_class  in IH2.
          exists (Ptrofs.unsigned(Ptrofs.repr x) + Ptrofs.unsigned(Ptrofs.repr x1) ).
          assert (A2: 0 <= (Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr x)))  + x1 <= Ptrofs.max_unsigned) by (eapply struct_in_bounds_field;eauto). 
          assert(A3:Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr x)) + x1 =
          Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr (Ptrofs.unsigned (Ptrofs.repr x) + Ptrofs.unsigned (Ptrofs.repr x1))))
          ).
          {
            rewrite <- (Ptrofs.add_unsigned).
            rewrite <- Ptrofs.add_assoc.
            rewrite (Ptrofs.add_unsigned (Ptrofs.add sofs (Ptrofs.repr x)) (Ptrofs.repr x1)) .
            rewrite (Ptrofs.unsigned_repr x1) ;auto.
            rewrite  (Ptrofs.unsigned_repr ((Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr x))) +x1) );auto.
            assert(M1: 0 <= x1) by ( eapply field_offset_in_range';eauto).
            assert(M2: 0 <= (Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr x))) ) by (eapply Ptrofs.unsigned_range)  .
            omega.
          }
          rewrite <-  A3.
          split;eauto.
          unfold bounded_struct_of_class.
          rewrite <-  A3.
          eapply find_pou_decl2find_pou in Find'.
          destruct Find'.
          eapply make_members_co in H8 as [co [F00 [F01 [F02[F03 [F04]]]] ]]  ; eauto.
          rewrite <- F02.
          split.
          - 
            eapply struct_in_struct_in_bounds;eauto.
            eapply Consistent;eauto.
            eapply field_translate_obj_type;eauto.
          -   
            assert (A01 : deref_loc (Clight.typeof (gen_exp po ex)) m sb (Ptrofs.add sofs (Ptrofs.repr x)) (Vptr sb (Ptrofs.add sofs (Ptrofs.repr x)))).
            {
            rewrite A11.
            now apply deref_loc_copy.
            }
            eapply eval_Elvalue with(v:= (Vptr sb  (Ptrofs.add sofs (Ptrofs.repr x)))) in IH3;eauto.
            eapply eval_Efield_struct in IH3; eauto.
            rewrite <- Ptrofs.add_unsigned.
            rewrite <- Ptrofs.add_assoc.
            apply IH3.
            rewrite Eq;eauto.
        Qed. 

        Lemma get_pou2struct :
          forall ex i0,
          get_pou_name (typeof ex) = Some i0 ->
          Clight.typeof (gen_exp po ex) = Tstruct i0 noattr.
        Proof.
          intros.
          rewrite type_pres.
          destruct (typeof ex) eqn:eq; inv H.
          auto.
        Qed.
        Lemma eval_exp_filed:
          forall ex i ty v ,
          wt_exp pro po (Field ex i ty) ->
          exp_eval me ve (Field ex i ty) (Some v) ->
          eval_expr tge e le m (gen_exp po (Field ex i ty)) v.
        Proof.
          intros.
          inv H.
          unfold get_class_by_type  in H4.
          destruct  (get_pou_name (typeof ex)) eqn:Eg;try inv H4.
          assert(Findpou'': exists pro',find_pou i0  pro =  Some (po0, pro')).
          {
            eapply find_pou_decl2find_pou;eauto.
          }
          destruct Findpou'' as [f1].
          rename H into Findpou''.
          edestruct make_members_co as (? & Hco & ? & Eq & ? & ?) ; eauto.
          inv H0.
          edestruct evall_field as (?&A0&A1&A2); eauto.
          simpl.
          edestruct staterep_field_offset as (d & ? & ?) ;eauto.
          eapply eval_Elvalue; eauto. 
          apply get_pou2struct in Eg.
          eapply eval_Efield_struct;eauto.
          + 
            eapply eval_Elvalue;eauto.
            rewrite Eg.
            now apply deref_loc_copy.
          + 
            rewrite Eq. eauto.
          +
            simpl.
            eapply staterep_deref_mem; eauto.
            rewrite Ptrofs.unsigned_repr_eq.
            assert( 0<=d < two_power_nat Ptrofs.wordsize ) as Hd.
            {
            assert (0 <= Ptrofs.unsigned (Ptrofs.add sofs (Ptrofs.repr x0)) <  Ptrofs.modulus) by apply Ptrofs.unsigned_range.
            unfold Ptrofs.max_unsigned.
            unfold Ptrofs.max_unsigned in H4.
            eapply field_offset_in_range' in H0;eauto.
            unfold Ptrofs.modulus in H4,H7.
            omega.
            }
            unfold Ptrofs.max_unsigned in Hd.
            unfold Ptrofs.modulus.
            rewrite Z.mod_small;eauto.
        Qed.

      End ExpField.

      Theorem expr_correct:
        forall ex v,
          wt_exp pro po ex ->
          exp_eval me ve ex (Some v) ->
          eval_expr tge e le m (gen_exp po ex) v.
      Proof. 
        induction ex ; intros * WTex Ev; inv Ev ; inv WTex; simpl.

        (* Var x ty : "x" *)
        Check eval_self_field.
        - apply eval_self_field;auto.

        (* temp x ty : "x" *)
        Check eval_temp_var.
        -  apply eval_temp_var;auto. 
        
        (* Const c ty : "c" *)
        - destruct c; constructor.

        (* Unop op e ty : "op e" *)
        - 
          Check match_states_conj.
          destruct u; simpl in *; econstructor; eauto;
            apply match_states_conj in Hmem as (?&?&?&?);auto; rewrite type_pres.
          Check sem_unary_operation_any_mem.
          + erewrite sem_unary_operation_any_mem; eauto.
            eapply wt_val_not_vptr; eauto.
          + match goal with
              H: match Ctyping.check_cast ?x ?y with _ => _ end = _ |- _ =>
              destruct (Ctyping.check_cast x y); inv H
            end.
            erewrite sem_cast_any_mem; eauto.
            eapply wt_val_not_vptr. eauto.

        (* Binop op e1 e2 : "e1 op e2" *)
        -  unfold translate_binop.
          econstructor; eauto.
          apply match_states_conj in Hmem as (?&?&?&?); rewrite 2 type_pres.
          erewrite sem_binary_operation_any_cenv_mem; eauto;
            eapply wt_val_not_vptr; eauto.
        - (*Field*)
        eapply eval_exp_filed.
        eapply wt_Field; eauto.
        rewrite <- H2.
        eapply efield;eauto.
      Qed.

    End ExprCorrectness.
End MatchStates.
End PRESERVATION.