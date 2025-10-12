(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Velus Require Import Common.
From Velus Require Import Environment.
From ST Require Import ST_Operators.
From Velus Require Import VelusMemory.
Require Import ST_Syntax.
Require Import ST_Semantics.
From Coq Require Import Morphisms.
From Coq Require Import List.
Import List.ListNotations.

From Hammer Require Import Hammer Reconstr.


Open Scope list_scope.

(** * Obc typing *)

(**

  Typing judgements for Obc and resulting properties.
  Classify Obc programs which are statically well-formed.

 *)

Module Type OBCTYPING
       (Import Ids   : IDS)
       (Import Op    : ST_OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : ST_SYNTAX Ids Op OpAux)
       (Import Sem   : ST_SEMANTICS Ids Op OpAux Syn).

  Section WellTyped.

    Variable pro     : project.
    Variable po      : pou_decl.
    Inductive wt_exp : exp -> Prop :=
    | wt_Var: forall x ty ,
        In (x,ty)  po.(pou_vars) ->
        wt_exp (Var x ty)
    | wt_Var_temp : forall x ty ,
        In (x,ty) po.(pou_temps) ->
        wt_exp (Var_temp x ty)
    | wt_Const: forall c,
        wt_exp (Const c)
    | wt_Unop: forall op e ty,
        type_unop op (typeof e) = Some ty ->
        wt_exp e ->
        wt_exp (Unop op e ty)
    | wt_Binop: forall op e1 e2 ty,
        type_binop op (typeof e1) (typeof e2) = Some ty ->
        wt_exp e1 ->
        wt_exp e2 ->
        wt_exp (Binop op e1 e2 ty)
    | wt_Field : forall ex id ty po ,
        get_class_by_type (typeof ex) pro = Some po ->
  
        In (id,ty)  po.(pou_vars) ->
        wt_exp ex ->
        wt_exp (Field ex id ty)
    (* | wt_Valid: forall x ty,
        In (x, ty) po.(pou_vars) ->
        wt_exp (Valid x ty) *)
    .

    Inductive wt_le : exp -> Prop :=
    | le1 : forall x ty,
        wt_exp (Var x ty) -> 
        wt_le (Var x ty)
    | le2 : forall x ty,
        wt_exp (Var_temp x ty)-> 
        wt_le (Var_temp x ty)
    | le3 : forall ex id ty,
        wt_exp (Field ex id ty)-> 
        wt_le (Field ex id ty).

    Inductive wt_stmt : stmt -> Prop :=
    | wt_Assign: forall le e  ,
        wt_le le ->
        wt_exp e ->
        implicit_cast (typeof e) (typeof le) ->
        wt_stmt (Assign le e)
    (* | wt_Ifte: forall e s1 s2,
        wt_exp e ->
        typeof e = bool_type ->
        wt_stmt s1 ->
        wt_stmt s2 ->
        wt_stmt (Ifte e s1 s2) *)
    | wt_Comp: forall s1 s2,
        wt_stmt s1 ->
        wt_stmt s2 ->
        wt_stmt (Comp s1 s2)
    (* | wt_Call: forall clsid po p' o f fm ys es,
        In (o, clsid) insts ->
        find_class clsid p = Some(po, p') ->
        find_method f po.(c_methods) = Some fm ->
        NoDup ys ->
        Forall2 (fun y xt => In (y, snd xt) po.(pou_vars)) ys fm.(m_out) ->
        Forall2 (fun e xt => typeof e = snd xt) es fm.(m_in) ->
        Forall wt_exp es ->
        wt_stmt (Call ys clsid o f es) *)
    | wt_Skip:
        wt_stmt Skip.

  End WellTyped.

  (**)
  Definition inst_type_has_decl(pro_l : list pou_decl)(ty : type) : option (pou_decl * list pou_decl) :=
    match get_pou_name ty  with 
      | None => None 
      | Some cls_name => find_pou cls_name pro_l
    end.  

   Definition wt_pou_decl_inst (pro:project) (pro_l : list pou_decl) (po: pou_decl) : Prop
    := (Forall (fun ocls=> inst_type_has_decl pro_l (snd ocls) <> None)  po.(pou_vars) ) /\
       (Forall (fun ocls=> get_pou_name (snd ocls) = None)  po.(pou_temps) )  /\
         wt_stmt pro po po.(pou_body) .

  Inductive wt_pou_decls(pro : project):  list pou_decl -> Prop :=
  | wtp_nil:
    wt_pou_decls pro  []
  | wtp_cons: forall po p,
      wt_pou_decl_inst pro p po ->
      wt_pou_decls pro p ->
      Forall (fun po' => po.(pou_name) <> po'.(pou_name)) p ->
      wt_pou_decls pro  (po::p).
  Definition wt_project(pro : project) :   Prop :=
    wt_pou_decls pro pro.

  Hint Constructors wt_exp wt_stmt  : obctyping.
  (*
  Instance wt_exp_Proper:
    Proper (@Permutation.Permutation (ident * type)
                                     ==> @Permutation.Permutation (ident * type)
                                     ==> @eq exp ==> iff) wt_exp.
  Proof.
    intros m2 m1 Hm v2 v1 Hv e' e He; subst.
    induction e; split; inversion_clear 1; constructor;
      try rewrite Hm in *;
      try rewrite Hv in *;
      repeat match goal with H:_ <-> _ |- _ => apply H; clear H end;
      auto with obctyping.
  Qed.

  Instance wt_stmt_Proper:
    Proper (@eq project
                ==> @Permutation.Permutation (ident * ident)
                ==> @Permutation.Permutation (ident * type)
                ==> @Permutation.Permutation (ident * type)
                ==> @eq stmt ==> iff) wt_stmt.
  Proof.
    intros p' p Hp xs2 xs1 Hxs ys2 ys1 Hys zs2 zs1 Hzs s' s Hs.
    rewrite Hp, Hs in *; clear Hp Hs.
    induction s; split; intro HH; inv HH.
    (* Assign *)
    - constructor; rewrite <-Hzs; try rewrite <-Hys; auto.
    - constructor; rewrite Hzs; try rewrite Hys; auto.
    (* AssignSt *)
    - constructor; try rewrite <-Hzs; rewrite <-Hys; auto.
    - constructor; try rewrite Hzs; rewrite Hys; auto.
    (* Ifte *)
    - constructor; try rewrite <-IHs1; try rewrite <-IHs2; auto;
        try rewrite <-Hzs; try rewrite <-Hys; auto.
    - constructor; try rewrite IHs1; try rewrite IHs2; auto;
        try rewrite Hzs; try rewrite Hys; auto.
    (* Comp *)
    - constructor; try rewrite <-IHs1; try rewrite <-IHs2; auto.
    - constructor; try rewrite IHs1; try rewrite IHs2; auto.
    (* Call *)
    - econstructor; eauto.
      * now rewrite <-Hxs.
      * match goal with H:Forall2 _ _ fm.(m_out) |- _ =>
                      apply Forall2_impl_In with (2:=H) end.
        intros; now rewrite <-Hzs.
      * match goal with H:Forall (wt_exp _ _) _ |- _ =>
                        apply Forall_impl with (2:=H) end.
        intros; now rewrite <-Hys, <-Hzs.
    - econstructor; eauto.
      * now rewrite Hxs.
      * match goal with H:Forall2 _ _ fm.(m_out) |- _ =>
                        apply Forall2_impl_In with (2:=H) end.
        intros; now rewrite Hzs.
      * match goal with H:Forall (wt_exp _ _) _ |- _ =>
                        apply Forall_impl with (2:=H) end.
        intros; now rewrite Hys, Hzs.
    (* Skip *)
    - constructor.
    - constructor.
  Qed.
  *)
  (** Properties *)
  Locate wt_val.
  Definition wt_venv_val (e: venv) (xty: ident * type) :=
    match Env.find  (fst xty) e with
    | None => True
    | Some v => wt_val v (snd xty)
    end.
  Check Forall.
  Definition wt_env (e: venv) (vars: list (ident * type)) :=
    Forall (wt_venv_val e) vars
    (* /\
    forall x ty (v:val), find_val x e  = Some v -> In (x, ty) (filter_val vars )  *)
    .

  Hint Unfold wt_env.

  Print find_inst.
  Inductive wt_mem : project -> menv -> pou_decl -> Prop :=
  | WTmenv: forall me pro po ,
      wt_env (values me) (filter_val (po.(pou_vars)) ) ->
      Forall (wt_mem_inst pro me) (filter_inst (po.(pou_vars)) )  -> 
      wt_mem pro me po 
  with wt_mem_inst :project -> menv ->  (ident * type) -> Prop :=
  (* | WTminst_empty: forall id me pro ty,
    find_inst id me = None ->
    wt_mem_inst pro me (id, ty) *)
  | WTminst: forall id me sub_env ty  pro po ,
      get_class_by_type ty pro  = Some po ->
      find_inst id me = Some sub_env ->
      wt_mem pro sub_env po ->
      wt_mem_inst pro me (id, ty) .

  Definition wt_state (pro: project) (me: menv) (ve: venv)(po : pou_decl)  : Prop :=
wt_mem pro me po /\ wt_env ve (filter_val po.(pou_temps)) .


Lemma wt_mem_inst_inv:
forall  pro me po x ty po' me',
wt_mem pro me po -> 
In (x,ty) (po.(pou_vars)) ->
get_class_by_type ty pro = Some po' ->
find_inst x me = Some me' ->
wt_mem pro me' po'.
Proof.
intros.
inv H.
assert(In (x,ty) (filter_inst (pou_vars po))).
{
 eapply filter_val_filter_In2;eauto.
 unfold get_class_by_type in H1.
 destruct (get_pou_name ty ) eqn:eq.
 eapply get_pou_name_inst;eauto.
 inv H1. 
}
eapply Forall_forall in H4;eauto.
inv H4.
rewrite H2 in H10.
inv H10.
inv H1.
rewrite H5 in H7.
inv H7.
eauto.
Qed. 

(* Lemma wt_mem_inv:
  forall pro me po l_idxs env',
  wt_mem pro me po ->
  me_idxs_get me l_idxs (Some env') ->
  wt_mem pro env' po.
Proof.
  intros H.
  induction l_idxs.
  + intros. inv H1.
  +
  intros.
  inv H1.
  admit.
  Admitted. *)
      

  (*
  (* XXX: why does this fail? *)
  (*
  Scheme wt_mem_ind_2 := Minimality for wt_mem Sort Prop
  with wt_mem_inst_ind_2 := Minimality for wt_mem_inst Sort Prop.
  Combined Scheme wt_mem_inst_ind' from wt_mem_ind_2, wt_mem_inst_ind_2.
  *)

  Section wt_mem_mult.

    Variable P : forall e p v_decl, wt_mem e p v_decl -> Prop.
    Variable Pinst : forall e p oc, wt_mem_inst e p oc -> Prop.

    Arguments P {e p v_decl} H.
    Arguments Pinst {e p oc} H.
    Arguments WTmenv {e p v_decl} Hwt Hinsts.
    Arguments WTminst_empty {e} p {o} c Hfind.
    Arguments WTminst {e p o c mo po p'} Hinst Hclass Hwt.

    Hypothesis WTmenvCase:
      forall e p v_decl
        (x : wt_env (values e) v_decl.(c_mems))
        (ys : Forall (wt_mem_inst e p) v_decl.(c_objs)),
        Forall (fun v_decl => exists H, @Pinst e p v_decl H) v_decl.(c_objs) ->
        @P e p v_decl (WTmenv x ys).

    Hypothesis WTminst_emptyCase:
      forall e p o c
        (Hfind: find_inst o e = None),
        Pinst (WTminst_empty p c Hfind).

    Hypothesis WTminstCase:
      forall e p o c mo po p'
        (Hfind_inst: find_inst o e = Some mo)
        (Hfind_class: find_class c p = Some (po, p'))
        (Hwt: wt_mem mo p' po),
        P Hwt ->
        Pinst (WTminst Hfind_inst Hfind_class Hwt).

    Fixpoint wt_mem_ind_mult {e p v_decl} (H: wt_mem e p v_decl) {struct H} : P H
    with wt_mem_inst_ind_mult {e p oc} (H: wt_mem_inst e p oc) {struct H}: Pinst H.
    - (* Define: wt_mem_ind_mult *)
      destruct H as [? ? ? Hwt Hrec].
      apply WTmenvCase.
      induction Hrec as [| ? ? Hwt' Hrec' ]; constructor; auto.
      exists Hwt'; auto.
    - (* Define: wt_mem_ind_inst_mult *)
      destruct H;
        clear wt_mem_inst_ind_mult;
        auto using WTminst_emptyCase, WTminstCase.
    Qed.

  End wt_mem_mult.

  Lemma wt_vempty:
    forall vars,
      wt_env vempty vars.
  Proof.
    induction vars as [|v vars]; auto.
    apply Forall_cons; auto.
    unfold wt_venv_val; rewrite menv.gempty; auto.
  Qed.

  Lemma wt_mempty:
    forall p po,
      wt_mem mempty p po.
  Proof.
    constructor.
    - now apply wt_vempty.
    - induction (po.(c_objs)) as [|(o, c) os]; auto.
      apply Forall_cons; auto.
      apply WTminst_empty.
      apply find_inst_gempty.
  Qed.
  Hint Resolve wt_vempty wt_mempty.
*)
  (* Lemma env_find_wt_val:
    forall l e x ty v ,
      wt_env e (filter_val l) ->
      In (x, ty)  l->
      find_val x e = Some v ->
      is_inst ty = false ->
      wt_val v ty.
  Proof.
    intros * WTe Hin Hfind Hinst.
    assert(In (x, ty)  (filter_val l) ).
    {
    unfold filter_val .
    rewrite filter_In.
    split;auto.
    unfold negb.
    simpl. rewrite Hinst. auto.  
    }
    apply Forall_forall with (1:=WTe) in H.
    unfold wt_venv_val in H.
    simpl in H.
    now rewrite Hfind in H.
  Qed. *)
  (* Lemma env_find_wt_inst:
    forall l e x ty v ,
      wt_env e (filter_inst l) ->
      In (x, ty) (filter_inst l)->
      find_val x e = Some v ->
      is_inst ty = true ->
      wt_val v ty.
  Proof.
    intros * WTe Hin Hfind Hinst.
    apply Forall_forall with (1:=WTe) in Hin.
    unfold wt_venv_val in Hin.
    simpl in Hin.
    now rewrite Hfind in Hin.
  Qed. *)

(*
  Lemma wt_program_find_class:
    forall clsid p po p',
      wt_program p ->
      find_class clsid p = Some (po, p') ->
      wt_class p' po /\ wt_program p'.
  Proof.
    induction p as [|po p]; [now inversion 2|].
    intros po' p' WTp Hfind.
    inversion Hfind as [Heq]; clear Hfind.
    inversion_clear WTp as [|? ? WTc WTp' Hnodup]; rename WTp' into WTp.
    destruct (ident_eq_dec po.(c_name) clsid) as [He|Hne].
    - subst. rewrite ident_eqb_refl in Heq.
      injection Heq; intros; subst. auto.
    - rewrite (proj2 (ident_eqb_neq po.(c_name) clsid) Hne) in Heq.
      apply IHp with (1:=WTp) (2:=Heq).
  Qed.

  Lemma wt_class_find_method:
    forall p po f fm,
      wt_class p po ->
      find_method f po.(c_methods) = Some fm ->
      wt_method p po.(c_objs) po.(c_mems) fm.
  Proof.
    intros p po f fm WTc Hfindm.
    destruct WTc as (Hfo & WTms).
    apply Forall_forall with (1:=WTms).
    apply find_method_In with (1:=Hfindm).
  Qed.
*)
 Lemma Forall_wt_mem_inst :
 forall f l x ty,
 Forall f (filter_inst l) -> 
 is_inst ty = true ->
 In (x, ty) l ->
 f (x, ty).
 Proof.
  intros.
  rewrite Forall_forall in H.
  apply H.
  unfold filter_inst .
  rewrite filter_In.
  split;auto.
  Qed.
  
  (* Lemma WTminst_1 :
  forall id me sub_env ty  pro po ,
        wt_mem_inst pro me (id, ty) ->
        get_class_by_type ty pro  = Some po ->
        find_inst id me = Some sub_env ->
        wt_mem pro sub_env po 
        .
  Proof.
  intros.
  eauto.
  assert(po = po0). {rewrite H0 in H4. inv H4;eauto. }
  assert(sub_env = sub_env0). {rewrite H1 in H7. inv H7;eauto. }
  subst;eauto. 
  Qed. *)

  (* Lemma exp_eval_inst_wt_mem:
  forall pro me ve ex po env' po' l_idxs,
  wt_state pro me ve po ->
  wt_exp pro po ex ->
  exp_eval_me_idxs me ve ex l_idxs ->
  me_idxs_get me l_idxs (Some env') ->
  get_class_by_type  (typeof ex) pro = Some po' ->
  wt_mem pro env' po'  .
  Proof.
    intros  .
    revert H3.
    revert H2.
    revert H1.
    revert po' env' l_idxs .
    induction ex ; intros ; inv H1;simpl in H3.
    + inv H.
      inv H0.
      inv H1.
      eapply Forall_wt_mem_inst  in H5;eauto.
      eapply WTminst_1 ;eauto.
      inv H2;eauto.
      inv H6.
    + 
    (*efield_inst*)
      inv H2.
      -  inv H9.
      - 
      inv H0.
      eapply IHex with(po':= po) in H11;eauto.
      inv H11.
      eapply Forall_wt_mem_inst  in H1;eauto.
      eapply WTminst_1 ;eauto.
    Qed. *)


  Lemma venv_find_wt_val:
    forall vars ve x ty v,
      wt_env ve vars ->
      In (x, ty) vars ->
      Env.find x ve = Some v ->
      wt_val v ty.
  Proof.
    (* sauto. *)
    intros * WTe Hin Hfind.
    apply Forall_forall with (1:=WTe) in Hin.
    unfold wt_venv_val in Hin.
    sauto.
  Qed.
  
  Lemma pres_sem_exp:
    forall pro me ve po ex v,
      wt_env (values me) (filter_val (pou_vars po)) ->
      wt_env ve (filter_val (pou_temps po)) -> 
      Forall (wt_mem_inst pro me) (filter_inst (pou_vars po)) ->
      (* Forall (wt_mem_inst pro me) (filter_inst (pou_temps po)) -> *)
      wt_exp pro po ex ->
      exp_eval me ve ex (Some v) ->
      wt_val v (typeof ex).
  Proof.
    assert(forall pro me ve l_idxs me' po0 po ex i t, 
    wt_state pro me ve po -> 
    exp_eval_me_idxs me ve (Field ex i t) l_idxs ->
    me_idxs_get me l_idxs (Some me') ->
    get_class_by_type (typeof (Field ex i t)) pro = Some po0 ->
    wt_exp pro po (Field ex i t) ->
    wt_mem pro me'  po0
    ).
    {
      intros pro me ve l_idxs me' po0 po.
      revert me' po0.
      induction l_idxs .
      + intros. inv H0.
      + intros.
      inv H0.
      destruct ex;simpl in *.
      -
      inv H1.
      inv H10.
      inv H3.
      eapply wt_mem_inst_inv;eauto.
      inv H11.
      inv H.
      inv H10.
      inv H4.
      eapply wt_mem_inst_inv;eauto.
      inv H5.
      - inv H10.
      - inv H10.
      - inv H10.
      - inv H10.
      - 
        inv H1.
        inv H10.
        inv H3.
      eapply wt_mem_inst_inv;eauto.
    }


  intros until v. intros WTm WTv WFv .
  assert(wt_state pro me ve po) by sauto.
  revert v.
  induction ex; intros v WTe Hexp.
  + 
   inv WTe. inv Hexp.
  unfold find_val in *.
  eapply venv_find_wt_val with (1:=WTm); eauto.
  + inv WTe. inv Hexp.
    eapply venv_find_wt_val with (1:=WTv); eauto.
  + inv Hexp. apply wt_val_const.
  + inv WTe. inv Hexp. eauto using pres_sem_unop.
  + inv WTe. inv Hexp. eauto using pres_sem_binop.
  +
    destruct ex;simpl.
    - 
    assert(A: wt_mem pro me po).
    {
      eapply WTmenv;eauto.
    }
    inv Hexp.
    inv WTe.
    inv H6.
    --
    inv H5.
    inv H10.
    eapply wt_mem_inst_inv in A;eauto.
    inv  A.
    (* inv H5. *)
    assert(A1:In (i,t) (filter_val (pou_vars po0))).
    {
      eapply filter_val_filter_In1;eauto. 
    }
    unfold wt_env in H1.
    unfold find_val in  H4.
    eapply Forall_forall in H1;eauto.
    unfold wt_venv_val  in H1; simpl in H1.
    sauto.
    --
    inv H5.
    inv H3.
    -inv Hexp; inv H5.
    -inv Hexp; inv H5.
    -inv Hexp; inv H5.
    -inv Hexp; inv H5.
    -inv Hexp. 
    inv WTe.

    eapply H in H0;eauto. 
    eauto.
    inv H4.
    inv H10.
    inv H0.
    unfold wt_env in H1.
    assert(In (i,t) (filter_val (pou_vars po0))).
    {
      eapply filter_val_filter_In1;eauto. 
    }
    eapply Forall_forall in H1;eauto.
    unfold wt_venv_val  in H1.
    unfold find_val in H2;simpl in H1 ; subst.
    rewrite H2 in H1.
    eauto.
  Qed.

  Lemma pres_sem_exp':
    forall pro me ve po ex v,
      wt_state pro me ve po ->
      wt_exp pro po ex ->
      exp_eval me ve ex (Some v) ->
      wt_val v (typeof ex).
  Proof.
    Reconstr.rsimple (@OBCTYPING.pres_sem_exp) (@OBCTYPING.wt_state, @Sem.menv).
  Qed.
  Hint Resolve pres_sem_exp'.
(*
  Lemma pres_sem_expo:
    forall mems vars me ve e vo,
      wt_env (values me) mems ->
      wt_env ve vars ->
      wt_exp mems vars e ->
      exp_eval me ve e vo ->
      wt_valo vo (typeof e).
  Proof.
    intros. destruct vo; simpl;
              eauto using pres_sem_exp.
  Qed.

  Lemma pres_sem_expo':
    forall prog c vars me ve e vo,
      wt_state prog me ve c vars ->
      wt_exp c.(c_mems) vars e ->
      exp_eval me ve e vo ->
      wt_valo vo (typeof e).
  Proof.
    intros. destruct vo; simpl; eauto.
  Qed.
  Hint Resolve pres_sem_expo'.

  Lemma pres_sem_exps:
    forall prog c vars me ve es vos,
      wt_state prog me ve c vars ->
      Forall (wt_exp c.(c_mems) vars) es ->
      Forall2 (exp_eval me ve) es vos ->
      Forall2 (fun e vo => wt_valo vo (typeof e)) es vos.
  Proof.
    intros; eapply Forall2_impl_In; eauto.
    intros. simpl in *.
    match goal with Hf:Forall _ ?xs, Hi: In _ ?xs |- _ =>
      apply Forall_forall with (1:=Hf) in Hi end.
    eapply pres_sem_expo'; eauto.
  Qed.
  Hint Resolve pres_sem_exps.
*)
  Lemma wt_venv_val_add:
    forall env v x y ty,
      (y = x /\ wt_val v ty) \/ (y <> x /\ wt_venv_val env (y, ty)) ->
      wt_venv_val (Env.add x v env) (y, ty).
  Proof.
    intros * Hor. unfold wt_venv_val; simpl.
    destruct Hor as [[Heq Hwt]|[Hne Hwt]].
    - subst. now rewrite Env.gss.
    - now rewrite Env.gso with (1:=Hne).
  Qed.

  Lemma wt_env_add:
    forall vars env x t v,
      NoDupMembers vars ->
      wt_env env vars ->
      In (x, t) vars ->
      wt_val v t ->
      wt_env (Env.add x v env) vars.
  Proof.
    intros * Hndup WTenv Hin WTv.
    unfold wt_env.
    induction vars as [|y vars]; auto.
    apply Forall_cons2 in WTenv.
    destruct WTenv as (WTx & WTenv).
    destruct y as (y & ty).
    apply nodupmembers_cons in Hndup.
    destruct Hndup as (Hnin & Hndup).
    inv Hin.
    - match goal with H:(y, ty) = _ |- _ => injection H; intros; subst end.
      constructor.
      + apply wt_venv_val_add; left; auto.
      + apply Forall_impl_In with (2:=WTenv).
        destruct a as (y & ty).
        intros Hin HTy.
        apply NotInMembers_NotIn with (b:=ty) in Hnin.
        apply wt_venv_val_add; right; split.
        intro; subst; contradiction.
        now apply HTy.
    - constructor.
      + apply wt_venv_val_add.
        destruct (ident_eq_dec x y);
          [subst; left; split|right]; auto.
        apply NotInMembers_NotIn with (b:=t) in Hnin.
        contradiction.
      + apply IHvars; auto.
  Qed.
  Hint Resolve wt_env_add.
Check wt_mem_inst.
  Lemma wt_mem_inst_add_val:
    forall pro o c x v me,
      wt_mem_inst pro me  (o, c) ->
      wt_mem_inst pro  (add_val x v me)  (o, c).
  Proof.
    intros.
    inv H.
    eapply WTminst;eauto.
  Qed.

Check wt_mem.
  Lemma wt_mem_add_val:
    forall pro  p x t v me,
      wt_mem pro me p  ->
      In (x, t) (filter_val  p.(pou_vars)) ->
      wt_val v t ->
      wt_mem pro (add_val x v me) p .
  Proof.
    inversion_clear 1; intros.
    constructor; simpl.
    - eapply wt_env_add; eauto.
      assert(NoDupMembers (filter_val (pou_vars p))).
      {
        pose proof (pou_nodupvars_vals p) as Nodup.
        apply NoDupMembers_filter.
        apply NoDupMembers_app_l in Nodup;eauto.
      }
      eauto.
    - apply Forall_forall; intros (?&?) Hin.
      eapply wt_mem_inst_add_val.
      eapply Forall_forall in Hin; eauto.
  Qed.
  Hint Resolve wt_mem_add_val.

  Corollary wt_state_add:
    forall prog me ve c  x v t,
      wt_state prog me ve c  ->
      NoDupMembers  (filter_val (pou_temps c)) ->
      In (x, t)  (filter_val (pou_temps c)) ->
      wt_val v t ->
      wt_state prog me (Env.add x v ve) c .
  Proof.
  intros. 
  unfold wt_state;split;
  destruct H; eauto.
  Qed.
  (*
  Hint Resolve wt_state_add.

  Corollary wt_state_adds:
    forall xs prog me ve c vars vs (xts: list (ident * type)),
      wt_state prog me ve c vars ->
      NoDupMembers vars ->
      Forall2 (fun y xt => In (y, snd xt) vars) xs xts ->
      NoDup xs ->
      Forall2 (fun rv xt => wt_val rv (snd xt)) vs xts ->
      wt_state prog me (Env.adds xs vs ve) c vars.
  Proof.
    induction xs; inversion 3; inversion 1; inversion 1; subst; auto.
    rewrite Env.adds_cons_cons; eauto.
  Qed.
  Hint Resolve wt_state_adds.

  Corollary wt_state_adds_opt:
    forall xs prog me ve c vars vs (xts: list (ident * type)),
      wt_state prog me ve c vars ->
      NoDupMembers vars ->
      Forall2 (fun y xt => In (y, snd xt) vars) xs xts ->
      NoDup xs ->
      Forall2 (fun rv xt => wt_val rv (snd xt)) vs xts ->
      wt_state prog me (Env.adds_opt xs (map Some vs) ve) c vars.
  Proof.
    intros; rewrite Env.adds_opt_is_adds; eauto.
  Qed.
  Hint Resolve wt_state_adds_opt.
*)
Check  wt_mem_inst .
Check wt_state.
  Corollary wt_state_add_val:
     forall prog me ve  po x v t,
      wt_state prog me ve po ->
      In (x, t) (filter_val (pou_vars po)) ->
      wt_val v t ->
      wt_state prog (add_val x v me) ve  po.
  Proof.
  intros * (?&?) ??; split.
  + eapply wt_mem_add_val;eauto.
  + eauto.
  Qed.
    (* intros * (?&?) ??; split; eauto. *)
  (* Qed. *)
  Hint Resolve wt_state_add_val.
(**
  Lemma wt_mem_inst_add_inst_neq:
    forall p o c x me_x me,
      wt_mem_inst me p (o, c) ->
      x <> o ->
      wt_mem_inst (add_inst x me_x me) p (o, c).
  Proof.
    inversion_clear 1.
    - left; rewrite find_inst_gso; auto.
    - eright; eauto.
      rewrite find_inst_gso; auto.
  Qed.

  Lemma wt_mem_inst_add_inst_eq:
    forall p c x po p' me_x me,
      wt_mem_inst me p (x, c) ->
      find_class c p = Some (po, p') ->
      wt_mem me_x p' po ->
      wt_mem_inst (add_inst x me_x me) p (x, c).
  Proof.
    inversion_clear 1; intros.
    - eright; eauto.
      apply find_inst_gss.
    - eright; eauto.
      apply find_inst_gss.
  Qed.

  Lemma wt_mem_add_inst:
    forall p c x c_x po p' me_x me,
      wt_mem me p c ->
      In (x, c_x) c.(c_objs) ->
      find_class c_x p = Some (po, p') ->
      wt_mem me_x p' po ->
      wt_mem (add_inst x me_x me) p c.
  Proof.
    inversion_clear 1 as [???? WT]; intros.
    constructor; simpl; auto.
    apply Forall_forall; intros (x', c') Hin.
    eapply Forall_forall in WT; eauto.
    destruct (ident_eq_dec x x').
    - subst.
      assert (c' = c_x) as ->
          by (eapply NoDupMembers_det; eauto using c_nodupobjs).
      eapply wt_mem_inst_add_inst_eq; eauto.
    - apply wt_mem_inst_add_inst_neq; auto.
  Qed.
  Hint Resolve wt_mem_add_inst.

  Corollary wt_state_add_inst:
     forall prog me ve c c' prog' vars x me_x c_x,
      wt_state prog me ve c vars ->
      In (x, c_x) (c_objs c) ->
      find_class c_x prog = Some (c', prog') ->
      wt_mem me_x prog' c' ->
      wt_state prog (add_inst x me_x me) ve c vars.
  Proof.
    intros * (?&?) ??; split; eauto.
  Qed.
  Hint Resolve wt_state_add_inst.

  Lemma wt_venv_val_remove:
    forall env x y ty,
      wt_venv_val env (y, ty) ->
      wt_venv_val (Env.remove x env) (y, ty).
  Proof.
    unfold wt_venv_val; simpl.
    intros * WTenv.
    destruct (ident_eq_dec x y); subst.
    now rewrite Env.grs.
    now rewrite Env.gro; auto.
  Qed.

  Lemma wt_env_remove:
    forall x env vars,
      wt_env env vars ->
      wt_env (Env.remove x env) vars.
  Proof.
    induction vars as [|(y, yt) vars]; auto.
    setoid_rewrite Forall_cons2.
    destruct 1 as (Hy & Hvars).
    split; [|now apply IHvars].
    now apply wt_venv_val_remove.
  Qed.
  Hint Resolve wt_env_remove.

  Lemma wt_env_adds_opt:
    forall vars env ys outs rvs,
      NoDupMembers vars ->
      NoDup ys ->
      wt_env env vars ->
      Forall2 (fun y (xt: ident * type) => In (y, snd xt) vars) ys outs ->
      Forall2 (fun vo xt => wt_valo vo (snd xt)) rvs outs ->
      wt_env (Env.adds_opt ys rvs env) vars.
  Proof.
    intros * NodupM Nodup WTenv Hin WTv.
    assert (length ys = length rvs) as Length
        by (transitivity (length outs); [|symmetry];
            eapply Forall2_length; eauto).
    revert env rvs outs WTenv WTv Length Hin.
    induction ys, rvs, outs; intros * WTenv WTv Length Hin;
      inv Length; inv Nodup; inv Hin; inv WTv; auto.
    destruct o.
    - rewrite Env.adds_opt_cons_cons'; auto.
      eapply IHys; eauto.
    - rewrite Env.adds_opt_cons_cons_None; auto.
      eapply IHys; eauto.
  Qed.
  Hint Resolve wt_env_adds_opt.

  Lemma wt_params:
    forall vos xs es,
      Forall2 (fun e vo => wt_valo vo (typeof e)) es vos ->
      Forall2 (fun e (xt: ident * type) => typeof e = snd xt) es xs ->
      Forall2 (fun vo xt => wt_valo vo (snd xt)) vos xs.
  Proof.
    induction vos, xs, es; intros * Wt Eq; inv Wt;
    inversion_clear Eq as [|? ? ? ? E]; auto.
    constructor; eauto.
    now rewrite <- E.
  Qed.
  Hint Resolve wt_params.

  Lemma wt_env_params:
    forall vos callee,
      Forall2 (fun vo xt => wt_valo vo (snd xt)) vos (m_in callee) ->
      wt_env (Env.adds_opt (map fst (m_in callee)) vos vempty) (meth_vars callee).
  Proof.
    intros * Wt.
    unfold wt_env.
    apply Forall_app.
    pose proof (m_nodupvars callee) as Nodup.
    split.
    - apply NoDupMembers_app_l in Nodup.
      apply wt_env_adds_opt with (outs:=m_in callee); eauto.
      + now apply fst_NoDupMembers.
      + clear; induction (m_in callee) as [|(?, ?)]; simpl; auto.
        constructor; auto.
        eapply Forall2_impl_In; eauto.
        intros; now right.
    - apply Forall_forall.
      intros (x, t) Hin.
      assert (~ In x (map fst (m_in callee))).
      { intro Hin'.
        apply in_map_iff in Hin'; destruct Hin' as [(x', t') [? Hin']]; simpl in *; subst.
        apply in_split in Hin; destruct Hin as (? & ? & Hin).
        apply in_split in Hin'; destruct Hin' as (? & ? & Hin').
        rewrite Hin, Hin' in Nodup.
        rewrite <-app_assoc, <-app_comm_cons in Nodup.
        apply NoDupMembers_app_r in Nodup.
        inversion_clear Nodup as [|? ? ? Notin].
        apply Notin.
        apply InMembers_app; right; apply InMembers_app; right; apply inmembers_eq.
      }
      unfold wt_venv_val; simpl.
      rewrite Env.find_In_gsso_opt, Env.gempty; auto.
  Qed.
  Hint Resolve wt_env_params.

  Lemma wt_env_params_exprs:
    forall vos callee es,
      Forall2 (fun e vo => wt_valo vo (typeof e)) es vos ->
      Forall2 (fun (e : exp) (xt : ident * type) => typeof e = snd xt) es (m_in callee) ->
      wt_env (Env.adds_opt (map fst (m_in callee)) vos vempty) (meth_vars callee).
  Proof.
    intros * Wt Eq.
    eapply wt_env_params, wt_params; eauto.
  Qed.
  Hint Resolve wt_env_params_exprs.

  Lemma pres_sem_stmt':
    (forall p me ve stmt e',
        stmt_eval p me ve stmt e' ->
        forall po vars,
          let (me', ve') := e' in
          NoDupMembers vars ->
          wt_program p ->
          wt_state p me ve po vars ->
          wt_stmt p po.(c_objs) po.(c_mems) vars stmt ->
          wt_mem me' p po /\ wt_env ve' vars)
    /\ (forall p me clsid f vs me' rvs,
          stmt_call_eval p me clsid f vs me' rvs ->
          forall p' po fm,
            wt_program p ->
            find_class clsid p = Some(po, p') ->
            find_method f po.(c_methods) = Some fm ->
            wt_mem me p' po ->
            Forall2 (fun v xt => wt_valo v (snd xt)) vs fm.(m_in) ->
            wt_mem me' p' po
            /\ Forall2 (fun v yt => wt_valo v (snd yt)) rvs fm.(m_out)).
  Proof.
    apply stmt_eval_call_ind.
    - (* assign *)
      intros * Hexp po vars Hndup WTp (WTm & WTe) WTstmt.
      split; auto.
      inv WTstmt. inversion_clear WTm as [? ? ? WTmv WTmi].
      eapply pres_sem_exp with (1:=WTmv) (2:=WTe) in Hexp; auto.
      eapply wt_env_add; eauto.
    - (* assign state *)
      intros * Hexp po vars Hndup WTp (WTm & WTe) WTstmt.
      split; auto.
      inv WTstmt. inversion_clear WTm as [? ? ? WTmv WTmi].
      eapply pres_sem_exp with (1:=WTmv) (2:=WTe) in Hexp; auto.
      constructor.
      + eapply wt_env_add; eauto.
        apply fst_NoDupMembers.
        now apply NoDup_app_weaken with (1:=po.(c_nodup)).
      + apply Forall_impl_In with (2:=WTmi).
        inversion 2; now eauto using wt_mem_inst.
    - (* call *)
      intros p * Hevals Hcall IH
             po vars Hndups WTp (WTm & WTe) WTstmt.
      inv WTstmt.
      edestruct IH; eauto; clear IH; simpl.
      + (* Instance memory is well-typed before execution. *)
        unfold instance_match; destruct (find_inst o me) eqn:Hmfind; auto.
        inversion_clear WTm as [? ? ? WTv WTi].
        eapply Forall_forall in WTi; eauto.
        inversion_clear WTi as [? ? ? ? Hmfind'|? ? ? ? ? ? ? Hmfind' Hcfind' WTm];
          rewrite Hmfind' in Hmfind; try discriminate.
        match goal with Hcfind:find_class _ _ = Some (_, p') |- _ =>
                        simpl in Hcfind'; rewrite Hcfind in Hcfind' end.
        injection Hmfind; injection Hcfind'. intros; subst.
        assumption.
      + (* Arguments are well-typed if given. *)
        rewrite Forall2_swap_args in Hevals.
        match goal with H:Forall2 _ es fm.(m_in) |- _ => rename H into Hes end.
        apply all_In_Forall2.
        now rewrite <-(Forall2_length _ _ _ Hes), (Forall2_length _ _ _ Hevals).
        intros x v Hin.
        apply Forall2_chain_In' with (1:=Hevals) (2:=Hes) in Hin.
        destruct Hin as (e & Hexp & Hty & Hxy & Hyv).
        rewrite <-Hty.
        apply in_combine_r in Hxy.
        match goal with H:Forall _ es |- _ =>
          apply Forall_forall with (1:=H) in Hxy end.
        eapply pres_sem_expo'; eauto; split; eauto.

    - (* sequential composition *)
      intros p menv env s1 s2
             * Hstmt1 IH1 Hstmt2 IH2 po vars Hndups WTp WTs WTstmt.
      inv WTstmt.
      (* match goal with WTstmt1:wt_stmt _ _ _ _ s1 |- _ => *)
      (*                 specialize (IH1 _ _ Hndups WTp WTs WTstmt1) end. *)
      edestruct IH1 as (WTm1 & WTe1); eauto.
      assert (wt_state p me1 ve1 po vars) as WTs1; auto; split; auto.
    - (* if/then/else *)
      intros prog me ve cond v b st sf env' menv'
             Hexp Hvtb Hstmt IH po vars Hndups WTp WTs WTstmt.
      apply IH; auto.
      inv WTstmt. destruct b; auto.
    - (* skip *)
      intros; auto.
    - (* call eval *)
      intros * Hfindc Hfindm Hlvos Hstmt IH Hrvs
             p'' po'' fm'' WTp Hfindc' Hfindm' WTmem WTv.
      rewrite Hfindc in Hfindc';
        injection Hfindc'; intros; subst po'' p''; clear Hfindc'.
      rewrite Hfindm in Hfindm';
        injection Hfindm'; intros; subst fm''; clear Hfindm'.
      destruct (wt_program_find_class _ _ _ _ WTp Hfindc) as (WTc & WTp').
      edestruct IH with (vars := meth_vars fm); eauto.
      + apply m_nodupvars.
      + split; eauto.
      + (* In a well-typed class, method bodies are well-typed. *)
        apply wt_class_find_method with (1:=WTc) (2:=Hfindm).
      + split; auto.
        (* Show that result values are well-typed. *)
        rewrite Forall2_map_1 in Hrvs.
        apply Forall2_swap_args in Hrvs.
        eapply Forall2_impl_In with (2:=Hrvs).
        intros v x Hvin Hxin Hxv.
        destruct x as (x & ty). simpl in *.
        destruct v; simpl; auto.
        eapply env_find_wt_val with (3:=Hxv);
          eauto using in_or_app.
  Qed.

  Lemma pres_sem_stmt:
    forall p po vars stmt me ve me' ve',
      NoDupMembers vars ->
      wt_program p ->
      wt_state p me ve po vars ->
      wt_stmt p po.(c_objs) po.(c_mems) vars stmt ->
      stmt_eval p me ve stmt (me', ve') ->
      wt_mem me' p po /\ wt_env ve' vars.
  Proof.
    intros.
    eapply ((proj1 pres_sem_stmt') _ _ _ _ (me', ve')); eauto.
  Qed.

  Lemma pres_sem_stmt_call:
    forall p clsid p' po f fm me vs me' rvs,
      wt_program p ->
      find_class clsid p = Some(po, p') ->
      find_method f po.(c_methods) = Some fm ->
      wt_mem me p' po ->
      Forall2 (fun vo xt => wt_valo vo (snd xt)) vs fm.(m_in) ->
      stmt_call_eval p me clsid f vs me' rvs ->
      wt_mem me' p' po
      /\ Forall2 (fun vo yt => wt_valo vo (snd yt)) rvs fm.(m_out).
  Proof.
    intros; eapply (proj2 pres_sem_stmt'); eauto.
  Qed.

  Lemma pres_loop_call_spec:
    forall n prog cid c prog' fid f ins outs me,
      wt_program prog ->
      find_class cid prog = Some (c, prog') ->
      find_method fid c.(c_methods) = Some f ->
      (forall n, Forall2 (fun vo xt => wt_valo vo (snd xt)) (ins n) f.(m_in)) ->
      wt_mem me prog' c ->
      loop_call prog cid fid ins outs 0 me ->
      exists me_n,
        loop_call prog cid fid ins outs n me_n
        /\ wt_mem me_n prog' c
        /\ Forall2 (fun vo xt => wt_valo vo (snd xt)) (outs n) f.(m_out).
  Proof.
    induction n; intros * ????? Loop.
    - exists me; split; auto; split; auto.
      inv Loop; eapply pres_sem_stmt_call; eauto.
    - edestruct IHn as (me_n & Loop_n & ? & ?); eauto.
      inversion_clear Loop_n as [???? Loop_Sn].
      assert (wt_mem me' prog' c) by (eapply pres_sem_stmt_call; eauto).
      eexists; split; eauto; split; auto.
      inv Loop_Sn.
      eapply pres_sem_stmt_call; eauto.
  Qed.

  Corollary pres_loop_call:
    forall prog cid c prog' fid f ins outs me,
      wt_program prog ->
      find_class cid prog = Some (c, prog') ->
      find_method fid c.(c_methods) = Some f ->
      (forall n, Forall2 (fun vo xt => wt_valo vo (snd xt)) (ins n) f.(m_in)) ->
      wt_mem me prog' c ->
      loop_call prog cid fid ins outs 0 me ->
      forall n, Forall2 (fun vo xt => wt_valo vo (snd xt)) (outs n) f.(m_out).
  Proof.
    intros; edestruct pres_loop_call_spec as (?&?&?&?); eauto.
  Qed.
*)
  (* Lemma wt_program_app:
    forall po po',
      wt_program (po ++ po') ->
      wt_program po'. *)
  Lemma wt_program_app:
    forall pro po po',
    wt_pou_decls pro (po ++ po') ->
    wt_pou_decls pro po'.
  Proof.
    induction po; inversion 1; auto.
  Qed.

(* Remark wt_program_not_class_in:
forall pre post o c cid,
  wt_program (pre ++ c :: post) ->
  In (o, cid) c.(c_objs) ->
  find_class cid pre = None. *)

  (* Remark wt_program_not_class_in:
    forall pre post o  cid po ty pro,
      wt_pou_decls pro (pre ++ po :: post) ->
      In (o, ty) (filter_inst (pou_vars po)) ->
      get_pou_name ty = Some cid ->
      find_pou cid pre = None.
  Proof.
    induction pre as [|k]; intros post o  cid po ty pro WT Hin Hname; auto.
    simpl in WT. inv WT.
    simpl.
    match goal with H: Forall _ _ |- _ => apply Forall_app_weaken, Forall_cons2 in H as (Hneq &?) end.
    apply ident_eqb_neq in Hneq.
    simpl.
    match goal with H:wt_pou_decls  _ _  |- _ =>
      specialize (IHpre _ _ _ _ _ _ H Hin Hname); apply wt_program_app in H;
        inversion_clear H as [|? ? WTc WTp Hnodup] end.
    destruct (ident_eqb k.(pou_name) cid) eqn: Heq; auto.
    apply ident_eqb_eq in Heq; rewrite Heq in *; clear Heq.
    inversion_clear WTc as [Ho Hm].
    assert(Hin':In (o, ty) (pou_vars po ++ pou_temps po)).
    {
      apply filter_In  in Hin as [Hin1  Hin2].
      apply in_app_iff.
      left;eauto.
    }
    admit. *)
    (* apply Forall_forall with (1:=Ho) in Hin'.
    simpl in Hin'.
    unfold inst_type_has_decl  in Hin'.
    apply not_None_is_Some in Hin'.
    destruct Hin' as ((po, p') & Hin').
    simpl in Hin'.
    destruct (get_pou_name ty).
    +
    rewrite <-(find_pou_name' _ _ _ _ Hin') in *.
    apply find_pou_In in Hin'.
    clear Hnodup.
    eapply Forall_forall in Hin'; eauto.
    simpl in Hin'.
    inv Hname;contradiction.
    +
    inv Hin'. *)

  (* Remark wt_program_not_same_name:
    forall post o c cid,
      wt_program (c :: post) ->
      In (o, cid) c.(c_objs) ->
      cid <> c.(c_name). *)
  (* Remark wt_program_not_same_name:
    forall post o po ty pro,
      wt_pou_decls pro (po :: post) ->
      In (o, ty) (filter_inst (pou_vars po)) ->
      (get_pou_name ty) <> Some (po.(pou_name)).
  Proof.
    intros * WTp Hin Hc'.
    (* rewrite Hc' in Hin; clear Hc'. *)
    inversion_clear WTp as [|? ? WTc WTp' Hnodup]; clear WTp'.
    inversion_clear WTc as [Ho Hm].
    assert(Hin':In (o, ty) (pou_vars po ++ pou_temps po)).
    {
    apply filter_In  in Hin as [Hin1  Hin2].
    apply in_app_iff.
    left;eauto.
    } *)
    (* apply Forall_forall with (1:=Ho) in Hin'.
    simpl in Hin'.
    unfold inst_type_has_decl  in Hin'.
    apply not_None_is_Some in Hin'.
    destruct Hin' as ((po, p') & Hin').
    simpl in Hin'.
    destruct (get_pou_name ty) eqn:eq.
    +
    rewrite <-(find_pou_name' _ _ _ _ Hin') in *.
    inv Hc'.
    apply find_pou_In in Hin'.
    eapply Forall_forall in Hin'; eauto.
    rewrite <- H0 in Hin'.
    eauto.
    +
    inv Hin'.
    Qed. *)

  Inductive suffix: list pou_decl -> list pou_decl -> Prop :=
    suffix_intro: forall p p',
      suffix p (p' ++ p).
(*
  Lemma suffix_refl:
    forall p, suffix p p.
  Proof.
    intro; rewrite <-app_nil_l; constructor.
  Qed.
  Hint Resolve suffix_refl.

  Add Parametric Relation: project suffix
      reflexivity proved by suffix_refl
        as suffix_rel.

  Lemma suffix_cons:
    forall po prog' prog,
      suffix (po :: prog') prog ->
      suffix prog' prog.
  Proof.
    intros * Hsub.
    inv Hsub.
    rewrite <-app_last_app. constructor.
  Qed.

  Remark find_class_sub_same:
    forall prog1 prog2 clsid po prog',
      find_class clsid prog2 = Some (po, prog') ->
      wt_program prog1 ->
      suffix prog2 prog1 ->
      find_class clsid prog1 = Some (po, prog').
  Proof.
    intros * Hfind WD Sub.
    inv Sub.
    induction p' as [|po' p']; simpl; auto.
    inversion_clear WD as [|? ? WTc WTp Hnodup].
    specialize (IHp' WTp).
    destruct (ident_eq_dec po'.(c_name) clsid) as [He|Hne].
    - rewrite He in *; clear He.
      rewrite <-(find_class_name _ _ _ _ IHp') in *.
      apply find_class_In in IHp'.
      eapply Forall_forall in IHp'; eauto; contradiction.
    - apply ident_eqb_neq in Hne.
      now rewrite Hne, IHp'.
  Qed.

  Lemma find_class_sub:
    forall prog clsid po prog',
      find_class clsid prog = Some (po, prog') ->
      suffix prog' prog.
  Proof.
    intros * Find.
    apply find_class_app in Find.
    destruct Find as (? & ? & ?); subst.
    rewrite List_shift_first.
    constructor.
  Qed.

  Lemma wt_stmt_sub:
    forall prog prog' insts mems vars s,
      wt_stmt prog' insts mems vars s ->
      wt_program prog ->
      suffix prog' prog ->
      wt_stmt prog insts mems vars s.
  Proof.
    induction 1; intros * Sub; econstructor; eauto.
    eapply find_class_sub_same; eauto.
  Qed.

  Lemma wt_mem_inst_sub:
    forall prog prog' mem oc,
      wt_mem_inst mem prog' oc ->
      wt_program prog ->
      suffix prog' prog ->
      wt_mem_inst mem prog oc.
  Proof.
    induction 1; intros.
    - left; auto.
    - eright; eauto.
      eapply find_class_sub_same; eauto.
  Qed.
  Hint Resolve wt_mem_inst_sub.

  Lemma wt_mem_sub:
    forall prog prog' c mem,
      wt_mem mem prog' c ->
      wt_program prog ->
      suffix prog' prog ->
      wt_mem mem prog c.
  Proof.
    induction 1 as [? ? ? ? WTmem_inst]; intros * Sub.
    constructor; auto.
    induction (c_objs cl) as [|(o, c)]; inv WTmem_inst; auto.
    constructor; eauto.
  Qed.

  Hint Constructors suffix.

  Lemma stmt_call_eval_suffix:
    forall p p' me clsid f vs ome rvs,
      stmt_call_eval p me clsid f vs ome rvs ->
      wt_program p' ->
      suffix p p' ->
      stmt_call_eval p' me clsid f vs ome rvs.
  Proof.
    intros * Ev ? ?.
    induction Ev.
    econstructor; eauto.
    eapply find_class_sub_same; eauto.
  Qed.
  Hint Resolve stmt_call_eval_suffix.

  Lemma stmt_eval_suffix:
    forall p p' me ve s S,
      stmt_eval p me ve s S ->
      wt_program p' ->
      suffix p p' ->
      stmt_eval p' me ve s S.
  Proof.
    intros * Ev ? ?.
    induction Ev; econstructor; eauto.
  Qed.
  Hint Resolve stmt_eval_suffix.

  Lemma find_class_chained:
    forall prog c1 c2 po prog' po' prog'',
      wt_program prog ->
      find_class c1 prog = Some (po, prog') ->
      find_class c2 prog' = Some (po', prog'') ->
      find_class c2 prog = Some (po', prog'').
  Proof.
    induction prog as [|c prog IH]; [now inversion 2|].
    intros * WTp Hfc Hfc'.
    simpl in Hfc.
    inversion_clear WTp as [|? ? WTc WTp' Hnodup].
    pose proof (find_class_In _ _ _ _ Hfc') as Hfcin.
    pose proof (find_class_name _ _ _ _ Hfc') as Hc2.
    destruct (ident_eq_dec c.(c_name) c1) as [He|Hne].
    - rewrite He, ident_eqb_refl in Hfc.
      injection Hfc; intros R1 R2; rewrite <-R1, <-R2 in *; clear Hfc R1 R2.
      assert (c.(c_name) <> po'.(c_name)) as Hne.
      + intro Hn.
        apply in_split in Hfcin.
        destruct Hfcin as (ws & xs & Hfcin).
        rewrite Hfcin in Hnodup.
        apply Forall_app_weaken in Hnodup; inv Hnodup.
        contradiction.
      + simpl. apply ident_eqb_neq in Hne.
        rewrite Hc2 in Hne. now rewrite Hne.
    - apply ident_eqb_neq in Hne.
      rewrite Hne in Hfc. clear Hne.
      rewrite <- (IH _ _ _ _ _ _ WTp' Hfc Hfc').
      (* inversion_clear Hnodup as [|? ? Hnin Hnodup']. *)
      apply find_class_app in Hfc.
      destruct Hfc as (po'' & Hprog & Hfc).
      rewrite Hprog in Hnodup.
      assert (c.(c_name) <> po'.(c_name)) as Hne.
      + intro Hn.
        apply in_split in Hfcin.
        destruct Hfcin as (ws & xs & Hfcin).
        rewrite Hfcin in Hnodup.
        apply Forall_app_weaken in Hnodup.
        rewrite app_comm_cons in Hnodup.
        apply Forall_app_weaken in Hnodup; inv Hnodup.
        contradiction.
      + simpl. rewrite <-Hc2. apply ident_eqb_neq in Hne.
        now rewrite Hne.
  Qed.

  Lemma wt_mem_chained:
    forall prog prog' c  mem ownerid owner,
      wt_program prog ->
      find_class ownerid prog = Some (owner, prog') ->
      wt_mem mem prog' c ->
      wt_mem mem prog c.
  Proof.
    intros.
    eapply wt_mem_sub; eauto.
    eapply find_class_sub; eauto.
  Qed.
  Hint Resolve wt_mem_chained.

  Lemma wt_mem_skip:
    forall prog prog' cid c mem,
      wt_program prog ->
      find_class cid prog = Some (c, prog') ->
      wt_mem mem prog c ->
      wt_mem mem prog' c.
  Proof.
    intros * WT Find WTm.
    inversion_clear WTm as [???? WTinsts]; constructor; auto.
    apply Forall_forall; intros (?&?) Hin.
    eapply Forall_forall in WTinsts; eauto.
    apply find_class_app in Find as (prog'' & ? &?); subst.
    pose proof WT as WT'.
    eapply wt_program_not_class_in in WT; eauto.
    inversion_clear WTinsts as [|???????? Find].
    * left; auto.
    * eright; eauto.
      rewrite find_class_app', WT in Find.
      apply wt_program_app in WT'.
      eapply wt_program_not_same_name in Hin; eauto.
      simpl in Find; cases_eqn E.
      apply ident_eqb_eq in E; congruence.
  Qed.
  Hint Resolve wt_mem_skip.

  Lemma find_class_rev:
    forall prog n c prog',
      wt_program prog ->
      find_class n prog = Some (c, prog') ->
      exists prog'', find_class n (rev prog) = Some (c, prog'').
  Proof.
   induction prog as [|c']; simpl; intros * WTP Find; try discriminate.
   inversion_clear WTP as [|? ? Hwtc Hwtp Hndup].
   erewrite find_class_app'; eauto.
   destruct (ident_eqb c'.(c_name) n) eqn:Heq.
   - inv Find.
     apply ident_eqb_eq in Heq.
     rewrite Heq in *.
     erewrite not_In_find_class; eauto.
      + simpl. apply ident_eqb_eq in Heq.
        rewrite Heq; econstructor; eauto.
      + rewrite map_rev.
        intro Hin.
        apply in_rev, in_map_iff in Hin as (?&?& Hin).
        eapply Forall_forall in Hin; eauto; congruence.
   - apply ident_eqb_neq in Heq.
     edestruct IHprog as (? & Find'); eauto.
     rewrite Find'.
     econstructor; eauto.
  Qed. *)

End OBCTYPING.

Module ObcTypingFun
       (Import Ids   : IDS)
       (Import Op    : ST_OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : ST_SYNTAX Ids Op OpAux)
       (Import Sem   : ST_SEMANTICS Ids Op OpAux Syn)
       <: OBCTYPING Ids Op OpAux Syn Sem.
  Include OBCTYPING Ids Op OpAux Syn Sem.
End ObcTypingFun.
