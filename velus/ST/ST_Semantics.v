From Coq Require Import FSets.FMapPositive.
From Coq Require Import Setoid.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Environment.
From ST Require Import ST_Operators.
From Velus Require Import VelusMemory.

Require Import ST_Syntax.
Require Import MyCommon.
(** * Obc semantics *)

(**

  The semantics of Obc relies on a tree-structure [memory], based
  on [Velus.VelusMemory], to store object instances and a [menv] to keep
  track of local variables during method calls.

 *)
Module Type ST_SEMANTICS
       (Import Ids   : IDS)
       (Import Op    : ST_OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : ST_SYNTAX Ids Op OpAux).

  Definition menv := memory val.
  Definition venv := env val.

  Definition mempty: menv := empty_memory _.
  Definition vempty: venv := Env.empty val.
  
  Definition instance_match (i: ident) (me: menv) : menv :=
    match find_inst i me with
    | None => mempty
    | Some i => i
    end.
  (**)
  Lemma instance_match_empty:
    forall x, instance_match x mempty = mempty.
    Proof.
      intros. unfold instance_match, find_inst; simpl.
      now rewrite Env.gempty.
    Qed.


  (*  ** 2.1 Evaluation of expressions *) 
  Section EXP_SEM.

    Inductive me_idxs_get(me: menv) : list ident -> option menv -> Prop  :=
    | meindex_get0:
      forall x ,
      me_idxs_get me [x] (find_inst x me)
    | meindex_get1:
      forall x l_idxs me',
      me_idxs_get me l_idxs (Some me') ->
      me_idxs_get me (x::l_idxs) (find_inst x me').

      (* me_idxs_replace idx sub_me  *)
    Inductive me_idxs_replace : list ident -> menv -> menv  -> menv -> Prop  :=
    | meindex_replace0:
      forall x me sub_me ,
      me_idxs_replace [x] sub_me me (add_inst x sub_me me)
    | meindex_replace1:
      forall x l_idxs me me' sub_me sub_me_up,
      me_idxs_get me l_idxs (Some sub_me_up)           ->
      me_idxs_replace   l_idxs    (add_inst x sub_me sub_me_up) me  me' ->
      me_idxs_replace (x::l_idxs) sub_me                        me  me'.

    Inductive exp_eval (me: menv) (ve: venv): exp -> option val -> Prop :=
      | evar:
          forall x ty ,
            is_inst ty = false ->
            exp_eval me ve (Var x ty) (find_val x me)
      | evar_temp :
          forall x ty ,
            is_inst ty = false ->
            exp_eval me ve (Var_temp x ty) (Env.find  x ve) 
      | econst:
          forall c,
            exp_eval me ve (Const c) (Some (sem_const c))
      | eunop :
          forall op exp c v ty,
            exp_eval me ve exp (Some c) ->
            sem_unop op c (typeof exp) = Some v ->
            exp_eval me ve (Unop op exp ty) (Some v)
      | ebinop :
          forall op e1 e2 c1 c2 v ty,
            exp_eval me ve e1 (Some c1) ->
            exp_eval me ve e2 (Some c2) ->
            sem_binop op c1 (typeof e1) c2 (typeof e2) = Some v ->
            exp_eval me ve (Binop op e1 e2 ty) (Some v)
      | efield :
          forall x ty ex l_idxs env',
            exp_eval_me_idxs me ve ex l_idxs ->
            me_idxs_get me l_idxs (Some env') ->
            is_inst ty = false ->
            exp_eval me ve (Field ex x ty) (find_val x env')
      with exp_eval_me_idxs (me: menv) (ve: venv): exp -> list ident -> Prop :=
        | einst :
          forall x ty ,
            is_inst ty = true ->
            exp_eval_me_idxs me ve (Var x ty) [x]
        (* | einst_temp :
          forall x ty ,
            is_inst ty = true ->
            exp_eval_me_idxs me ve (Var_temp x ty) [x] *)
        | efield_inst :
          forall x ty ex l_idxs,
            is_inst ty = true ->
            exp_eval_me_idxs me ve ex l_idxs ->
            exp_eval_me_idxs me ve (Field ex x ty) (x::l_idxs)
      .
      

      
  End EXP_SEM.

  (*  ** 2.2 Transition semantics for statements and functions  *) 
  Section STMT_SEM.


  Inductive assign_val_eval :
    project -> menv -> venv -> stmt -> menv * venv -> Prop :=
      | Iassign_var:
          forall prog me ve x e v ty,
          exp_eval me ve e (Some v) ->
          assign_val_eval prog me ve (Assign  (Var x ty) e) (add_val x v me, ve)
      | Iassign_temp:
          forall prog me ve x e v ty,
            exp_eval me ve e (Some v) ->
            assign_val_eval prog me ve (Assign  (Var_temp x ty) e) (me, Env.add x v ve)
      | Iassign_field:
          forall prog me ve ex x e v ty l_idsx sub_me me',
            exp_eval me ve e (Some v) ->
            exp_eval_me_idxs me ve ex l_idsx -> 
            me_idxs_get me l_idsx (Some sub_me) ->
            me_idxs_replace l_idsx (add_val x v sub_me) me me' -> 
            assign_val_eval prog me ve (Assign  (Field ex x ty) e) (me', ve).



  Inductive stmt_eval:
    project -> menv -> venv -> stmt -> menv * venv -> Prop :=
    | Iassign_val :
      forall prog me ve le e me' ve' ,
      assign_val_eval prog me ve (Assign le e) (me' , ve') ->
      stmt_eval       prog me ve (Assign le e) (me' , ve')
    | Iassign_inst :
      forall prog me ve le e l_idxs_l l_idxs_r me' me_sub,
      exp_eval_me_idxs me ve le l_idxs_l ->
      exp_eval_me_idxs me ve e  l_idxs_r ->
      me_idxs_get me l_idxs_r (Some me_sub) ->
      me_idxs_replace l_idxs_l me_sub me me' ->
      stmt_eval       prog me ve (Assign le e) (me' , ve)
    | Icall:
        forall  pro me ve id ty pou_id me_sub me_sub' pdecl ve_sub,
          get_pou_name ty = Some pou_id ->
          find_pou_decl pou_id pro = Some pdecl ->
          find_inst id me =  Some me_sub ->
          stmt_eval pro  me_sub vempty pdecl.(pou_body) (me_sub' , ve_sub)  ->
          stmt_eval pro me ve (Call (Var id ty) ) (add_inst id me_sub' me, ve)
    | Icomp:
        forall  pro me ve  a1 a2 ve1 me1 ve2 me2,
          stmt_eval pro me ve a1 (me1, ve1) ->
          stmt_eval pro me1 ve1 a2 (me2, ve2) ->
          stmt_eval pro me ve (Comp a1 a2) (me2, ve2)
    (* | Iifte:
        forall pro me ve cond v b ifTrue ifFalse ve' me',
          exp_eval me ve cond (Some v) ->
          val_to_bool v = Some b ->
          stmt_eval pro me ve (if b then ifTrue else ifFalse) (me', ve') ->
          stmt_eval pro me ve (Ifte cond ifTrue ifFalse) (me', ve') *)
    | Iskip:
          forall pro me ve,
          stmt_eval pro me ve Skip (me, ve)
    .

    Scheme stmt_eval_ind_2 := Minimality for stmt_eval Sort Prop.
    Combined Scheme stmt_eval_call_ind from stmt_eval_ind_2.
  End STMT_SEM.




End ST_SEMANTICS.


Module ST_SemanticsFun
       (Import Ids   : IDS)
       (Import Op    : ST_OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : ST_SYNTAX Ids Op OpAux) <: ST_SEMANTICS Ids Op OpAux Syn.
  Include ST_SEMANTICS Ids Op OpAux Syn.
End ST_SemanticsFun.