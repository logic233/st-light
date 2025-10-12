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





End ST_SEMANTICS.


Module ST_SemanticsFun
       (Import Ids   : IDS)
       (Import Op    : ST_OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Syn   : ST_SYNTAX Ids Op OpAux) <: ST_SEMANTICS Ids Op OpAux Syn.
  Include ST_SEMANTICS Ids Op OpAux Syn.
End ST_SemanticsFun.