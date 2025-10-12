
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



Module Type ST_TYPING
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
        is_inst ty = false ->
        wt_exp (Var_temp x ty)
    | wt_Const: forall c,
        wt_exp (Const c)
    | wt_Unop: forall op ex ty,
        type_unop op (typeof ex) = Some ty ->
        wt_exp ex ->
        wt_exp (Unop op ex ty)
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
      .
    Inductive inst_cast(pro: project)(ty1:type)(ty2:type) : Prop :=
    | inst_cast0 :
      get_class_by_type ty1 pro  = Some po ->
      get_class_by_type ty2 pro  = Some po ->
      inst_cast pro ty1 ty2.

    Inductive wt_stmt : stmt -> Prop :=
    | wt_Assign_Var: forall x ty ex ,
        wt_exp (Var x ty) ->
        wt_exp ex ->
        implicit_cast (typeof ex) ty ->
        wt_stmt (Assign (Var x ty) ex)
    | wt_Assign_temp: forall x ty  ex  ,
        wt_exp (Var_temp x ty) ->
        wt_exp ex ->
        ty = (typeof ex) ->
        wt_stmt (Assign (Var_temp x ty) ex)
    | wt_Assign_Field: forall ex1 id  ex  ty,
        wt_exp (Field ex1 id ty) ->
        wt_exp ex ->
        implicit_cast (typeof ex) ty ->
        wt_stmt (Assign (Field ex1 id ty) ex)
    | wt_Assign_Var_inst: forall x ty ex,
        wt_exp (Var x ty) ->
        wt_exp ex ->
        inst_cast pro (typeof ex) ty  ->
        wt_stmt (Assign (Var x ty) ex)
    | wt_Call: forall x ty,
        wt_exp (Var x ty) ->
        get_class_by_type ty pro = Some po ->
        wt_stmt (po.(pou_body)) ->
        wt_stmt (Call (Var x ty))
    | wt_If: forall s1 s2 ex,
        wt_exp ex ->
        wt_stmt s1 ->
        wt_stmt s2 ->
        wt_stmt (If ex s1 s2)
    | wt_Repeat: forall s ex,
        wt_exp ex ->
        wt_stmt s ->
        wt_stmt (Repeat s ex)
    | wt_Reset: forall x ty,
        wt_exp (Var x ty) ->
        get_class_by_type ty pro = Some po ->
        wt_stmt (po.(pou_body)) ->
        wt_stmt (Reset (Var x ty))
    | wt_Return:
        wt_stmt Return
    | wt_Exit:
        wt_stmt Exit
    | wt_Continue:
        wt_stmt Continue
    | wt_Comp: forall s1 s2,
        wt_stmt s1 ->
        wt_stmt s2 ->
        wt_stmt (Comp s1 s2)
    | wt_Skip:
        wt_stmt Skip.

  End WellTyped.

  (**)
  Definition inst_type_has_decl(pro_l : list pou_decl)(ty : type) : option (pou_decl * list pou_decl) :=
    match get_pou_name ty  with 
      | None => None 
      | Some po_name => find_pou po_name pro_l
    end.  

   Definition wt_pou (pro:project)  (po: pou_decl) : Prop
    := (Forall (fun po=> inst_type_has_decl pro (snd po) <> None)  po.(pou_vars) ) /\
       (Forall (fun po=> get_pou_name (snd po) = None)  po.(pou_temps) )  /\
         wt_stmt pro po po.(pou_body) .

  Inductive wt_project:  project -> Prop :=
  | wtp_nil:
    wt_project  []
  | wtp_cons: forall po p,
      wt_pou p po ->
      wt_project  p ->
      Forall (fun po' => po.(pou_name) <> po'.(pou_name)) p ->
      wt_project (po::p).

  (* Hint Constructors wt_exp wt_stmt  . *)
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
    simpl in Hin.
    destruct (Env.find x ve)  eqn:eq.
    inv Hfind;eauto.
    inv Hfind.
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
      --
      inv H10.
      --
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
    Reconstr.rsimple (@ST_TYPING.pres_sem_exp) (@ST_TYPING.wt_state, @Sem.menv).
  Qed.
  Hint Resolve pres_sem_exp'.

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

  Lemma wt_program_app:
    forall po pro,
    wt_project (po ++ pro) ->
    wt_project pro.
  Proof.
    induction po; inversion 1; auto.
  Qed.

  Remark wt_program_not_class_in:
    forall pre post ty po i pou_nm,
      wt_project (pre ++ po :: post) ->
      In (i, ty) po.(pou_vars) ->
      get_pou_name ty = Some pou_nm ->
      find_pou pou_nm pre = None.
  Proof.
    induction pre as [|k]; intros post ty po i pou_nm WT Hin TY; auto.
    simpl in WT. inv WT.
    simpl.
    match goal with H: Forall _ _ |- _ => apply Forall_app_weaken, Forall_cons2 in H as (Hneq &?) end.
    apply ident_eqb_neq in Hneq.
    simpl.
    assert(WTc:wt_pou post po).
    {
      eapply wt_program_app in H2.
      inv H2;eauto.
    }
    destruct (ident_eqb (pou_name k) pou_nm) eqn: Heq; auto.
    +
    apply ident_eqb_eq in Heq; rewrite Heq in *; clear Heq.
    inversion_clear WTc as [Ho Hm].
    apply Forall_forall with (1:=Ho) in Hin.
    apply not_None_is_Some in Hin.
    destruct Hin as ((po', p') & Hin).
    simpl in Hin.
    inv Hin.
    unfold inst_type_has_decl  in H3.
    destruct (get_pou_name ty) eqn:POU; try discriminate.
    assert(A:pou_name po' = pou_nm).
    {
        eapply find_pou2find_pou_decl in H3.
        eapply find_pou_name in H3;subst.
        inv TY;eauto.
    }

    apply find_pou_In in H3.
    eapply Forall_forall in H3; eauto.
    rewrite <- A in H3; try congruence.
  +
    eapply IHpre in H2;eauto.
  Qed.


  Remark wt_program_not_same_name:
    forall post o c  pou_nm ty,
      wt_project (c :: post) ->
      In (o, ty) c.(pou_vars) ->
      get_pou_name ty = Some pou_nm ->
      pou_nm <> c.(pou_name).
  Proof.
    intros * WTp Hin TY Hc'.
    inversion_clear WTp as [|? ? WTc WTp' Hnodup]; clear WTp'.
    subst.
    inversion_clear WTc as [Ho Hm].
    apply Forall_forall with (1:=Ho) in Hin.
    apply not_None_is_Some in Hin.
    destruct Hin as ((po, p') & Hin).
    simpl in Hin.
    unfold inst_type_has_decl  in Hin.

    destruct (get_pou_name ty) eqn:POU; try discriminate;subst.
    

    assert(A:pou_name po = pou_name c).
    {
    inv TY.
    eapply find_pou2find_pou_decl in Hin.
    apply find_pou_name in Hin.
    eauto.
    }
    rewrite <- A in Hnodup.
    eapply find_pou_In in Hin.
    eapply Forall_forall in Hin; eauto.
    congruence.
    Qed.

  Inductive suffix: list pou_decl -> list pou_decl -> Prop :=
    suffix_intro: forall p p',
      suffix p (p' ++ p).

  Lemma find_class_chained:
    forall prog c1 c2 po prog' po' prog'',
      wt_project prog ->
      find_pou c1 prog = Some (po, prog') ->
      find_pou c2 prog' = Some (po', prog'') ->
      find_pou c2 prog = Some (po', prog'').
  Proof.
    induction prog as [|c prog IH]; [now inversion 2|].
    intros * WTp Hfc Hfc'.
    simpl in Hfc.
    inversion_clear WTp as [|? ? WTc WTp' Hnodup].
    pose proof (find_pou_In _ _ _ _ Hfc') as Hfcin.
    pose proof (find_pou_name' _ _ _ _ Hfc') as Hc2.
    destruct (ident_eq_dec (pou_name c) c1) as [He|Hne].
    - rewrite He, ident_eqb_refl in Hfc.
      injection Hfc; intros R1 R2; rewrite <-R1, <-R2 in *; clear Hfc R1 R2.
      assert (pou_name c <> pou_name po') as Hne.
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
      apply find_pou_app in Hfc.
      destruct Hfc as (po'' & Hprog & Hfc).
      rewrite Hprog in Hnodup.
      assert (pou_name c <> pou_name po') as Hne.
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

End ST_TYPING.

Module ST_TypingFun
       (Import Ids   : IDS)
       (Import Op    : ST_OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : ST_SYNTAX Ids Op OpAux)
       (Import Sem   : ST_SEMANTICS Ids Op OpAux Syn)
       <: ST_TYPING Ids Op OpAux Syn Sem.
  Include ST_TYPING Ids Op OpAux Syn Sem.
End ST_TypingFun.
