From Velus Require Import Common.
Require Import ST_Operators.

Open Scope bool_scope.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.


Module Type ST_SYNTAX
       (Import Ids : IDS)
       (Import Op : ST_OPERATORS)
       (Import OpAux : OPERATORS_AUX Op).

  Inductive exp : Type :=
    | Var   : ident -> type -> exp                (* variable  *)
    | Var_temp : ident -> type -> exp             (* variable  *)
    | Const : const-> exp                         (* constant *)
    | Unop  : unop -> exp -> type -> exp          (* unary operator *)
    | Binop : binop -> exp -> exp -> type -> exp  (* binary operator *)
    | Field : exp -> ident -> type -> exp
  .
  Fixpoint typeof (e: exp): type :=
    match e with
    | Const c => type_const c
    | Var _ ty
    | Var_temp _ ty
    | Unop _ _ ty
    | Binop _ _ _ ty 
    | Field _ _ ty => ty
    end.

  Inductive stmt : Type :=
  | Assign : exp -> exp -> stmt                    (* x = e *)
  | Call : exp -> stmt                   (*call*)
  | Reset : exp -> stmt                        (*reset*)
  | Skip : stmt 
  | Comp : stmt -> stmt -> stmt                      (* s1; s2 *)
  .


  Record pou_decl : Type :=
    mk_pou {
        pou_name : ident;

        pou_vars : list(ident * type);
        pou_temps : list(ident * type);
        pou_body : stmt;
        pou_reset : stmt;
        pou_nodupvars_vals  : NoDupMembers (pou_vars ++ pou_temps );
        pou_good :Forall ValidId (pou_vars ++ pou_temps );
      }.


  Lemma pou_nodup_vars:
    forall po, NoDupMembers (pou_vars po).
  Proof.
    intro.
    pose proof (pou_nodupvars_vals po) as Nodup.
    eapply NoDupMembers_app_l;eauto.
  Qed.

  Lemma pou_nodup_temps:
    forall po, NoDupMembers (pou_temps po).
  Proof.
    intro.
    pose proof (pou_nodupvars_vals po) as Nodup.
    eapply NoDupMembers_app_r;eauto.
  Qed.

  Lemma InMembers_exist:
    forall(A:Type)(B:Type) (i:A) l ,
    (exists (t:B) , In (i, t) l) ->
    InMembers i l.
  Proof.
  intros A B i l H.
  destruct H as [t HIn].
  induction l as [| [a b] l' IH].
  - (* Case: l is empty *)
    simpl in HIn. contradiction.
  - (* Case: l is (a, b) :: l' *)
    simpl in HIn. simpl.
    destruct HIn as [H_eq | H_in].
    + (* Case: (i, t) = (a, b) *)
      inversion H_eq. subst. left. reflexivity.
    + (* Case: In (i, t) l' *)
      right. apply IH. auto.
  Qed.

  (* Hint Resolve pou_nodupvars. *)



  (* Lemma m_nodupin:
    forall f, NoDupMembers (pou_temp f).
  Proof.
    intro; pose proof (pou_nodupvars f) as Nodup.
    now apply NoDupMembers_app_r in Nodup.
  Qed.

  Lemma pou_nodupvars':
    forall f, NoDupMembers (pou_var f).
  Proof.
    intro; pose proof (pou_nodupvars f) as Nodup;
    now apply NoDupMembers_app_l in Nodup.
  Qed. *)

  (* Record project: Type := mk_project{
    pou_decls: list pou_decl;
  }. *)
  Definition project : Type := list pou_decl.
  Definition find_pou (n: ident) : list pou_decl -> option (pou_decl * list pou_decl) :=
    fix find p := match p with
                  | [] => None
                  | c :: p' => if ident_eqb c.(pou_name) n
                              then Some (c, p') else find p'
                  end.
  
  Definition find_pou_decl (f: ident): list pou_decl -> option pou_decl :=
    fix find ms := match ms with
                   | [] => None
                   | m :: ms' => if ident_eqb m.(pou_name) f
                                then Some m else find ms'
                   end.

  Lemma find_pou_decl2find_pou:
    forall pro_l id po ,
    find_pou_decl pro_l id = Some po ->
    exists pro_l', find_pou pro_l id = Some (po,pro_l')
  .
  Proof.
  intros id pro_l po H.
  induction pro_l  as [|hd tl IH].
  - simpl in H. discriminate H.
  - simpl in H. simpl.
    destruct (ident_eqb (pou_name hd) id) eqn:Heq.
    + inversion H; subst; clear H.
      exists tl.  reflexivity.
    + apply IH in H. destruct H as [pro_l' H].
      exists pro_l'. simpl.  assumption.
  Qed.
      
  Lemma find_pou2find_pou_decl:
  forall pro_l id po pro_l',
  find_pou  id pro_l = Some (po,pro_l') ->
  find_pou_decl  id pro_l = Some po 
.
Proof.
  intros.
  induction pro_l  as [|hd tl IH].
  discriminate H.
  - simpl in H. simpl.
    destruct (ident_eqb (pou_name hd) id) eqn:Heq.
    + inversion H; subst; clear H.
      auto.
    + apply IH in H. auto.
Qed.
  Remark find_pou_name:
    forall p_l po po_id,
      find_pou_decl po_id p_l = Some po ->
      po.(pou_name) = po_id.
    Proof.
    intros * Hfind.
    induction p_l; inversion Hfind as [H].
    destruct (ident_eqb (pou_name a) po_id) eqn: E.
    - inversion H; subst.
      now apply ident_eqb_eq.
    - now apply IHp_l.
    Qed.

  Remark find_pou_name':
    forall id po c po',
      find_pou id po = Some (c, po') ->
      c.(pou_name) = id.
  Proof.
    intros * Hfind.
    induction po; inversion Hfind as [H].
    destruct (ident_eqb (pou_name a) id) eqn: E.
    - inversion H; subst.
      now apply ident_eqb_eq.
    - now apply IHpo.
  Qed.

  (* Remark find_class_In:
    forall id po c po',
      find_class id po = Some (c, po') ->
      In c po. *)
  Remark find_pou_In:
    forall id po c po',
      find_pou id po = Some (c, po') ->
      In c po.
  Proof.
    intros * Hfind.
    induction po; inversion Hfind as [H].
    destruct (ident_eqb (pou_name  a) id) eqn: E.
    - inversion H; subst.
      apply in_eq.
    - apply in_cons; auto.
  Qed.

  Lemma find_pou_none:
    forall ponm po prog,
      find_pou ponm (po::prog) = None
      <-> (po.(pou_name) <> ponm /\ find_pou ponm prog = None).
  Proof.
    intros ponm po prog.
    simpl; destruct (ident_eqb (pou_name po) ponm) eqn: E.
    - split; intro HH; try discriminate.
      destruct HH.
      apply ident_eqb_eq in E; contradiction.
    - apply ident_eqb_neq in E; split; intro HH; tauto.
  Qed.
  Remark find_pou_app:
    forall id po c po',
      find_pou id po = Some (c, po') ->
      exists po'',
        po = po'' ++ c :: po'
        /\ find_pou id po'' = None.
  Proof.
    intros * Hfind.
    induction po; inversion Hfind as [H].
    destruct (ident_eqb (pou_name a) id) eqn: E.
    - inversion H; subst.
      exists nil; auto.
    - specialize (IHpo H).
      destruct IHpo as (po'' & Hcls'' & Hnone).
      rewrite Hcls''.
      exists (a :: po''); split; auto.
      simpl; rewrite E; auto.
  Qed.

  Remark find_pou_decl_In:
    forall id po_l po,
    find_pou_decl id po_l = Some po ->
    In po po_l.
  Proof.
    intros.
    induction po_l; inversion H.
    destruct (ident_eqb (pou_name a) id) eqn:E.
    - inversion H1. apply in_eq.
    - apply in_cons;eauto.
  Qed.

  Definition filter_val(l:list (ident * type)) : list (ident * type) :=
  filter (fun x=> negb (is_inst (snd x))) l .

  Definition filter_inst(l:list (ident * type)) : list (ident * type) :=
  filter (fun x=>  (is_inst (snd x))) l .

  Definition get_class_by_type (ty : type)(pro:project) : option pou_decl :=
    match get_pou_name ty with
      | None => None
      | Some cls_name => find_pou_decl cls_name pro
    end.
  Lemma filter_val_filter_In1:
    forall i t l,
    is_inst t = false ->
    In (i, t) l ->
    In (i, t) (filter_val l)
  .
  Proof.
    intros.
    unfold filter_val.
    apply filter_In.
    split;auto.
    simpl.
    rewrite H.
    auto.
  Qed.

  Lemma filter_val_filter_In2:
    forall i t l,
    is_inst t = true ->
    In (i, t) l ->
    In (i, t) (filter_inst l)
  .
  Proof.
    intros.
    unfold filter_inst.
    apply filter_In.
    split;auto.
  Qed. 

  Axiom var_notreserved:
  forall po x ty,
  In (x, ty) (pou_temps po ++ pou_vars po)
  -> ~ In x reserved.


  Lemma filter_InMembers :
  forall A B (a : A) f (l : list (A * B)),
    InMembers a (filter f l) -> InMembers a l.
  Proof.
    intros.
    induction l ;eauto.
    simpl in H. simpl.
    destruct a0.
    destruct  (f (a0, b)) eqn:H1.
    + simpl in H.
      destruct H;eauto.
    + apply IHl in H. 
      eauto.
  Qed.

    


  Theorem NoDupMembers_filter  : 
  forall A B (l : list(A*B)) f,
  NoDupMembers l -> 
  NoDupMembers (filter f l).
  Proof.
  intros A B l f H.
  induction H as [|a b l Hnin Hnodup IH].
  - 
    simpl. apply NoDupMembers_nil.
  - 
    simpl. destruct (f (a, b)) eqn:Hf.
    + (* f (a, b) = true *)
      apply NoDupMembers_cons.
      * (* ~ InMembers a (filter f l) *)
        contradict Hnin. eapply filter_InMembers;eauto.
        (* destruct Hnin as [Hin Hf'].
        exact Hin. *)
      * (* NoDupMembers (filter f l) *)
        apply IH.
    + (* f (a, b) = false *)
      apply IH.
Qed.


Lemma po_notreserved:
  forall x po,
    In x reserved ->
    ~InMembers x ( po.(pou_vars) ++ po.(pou_temps) ).
Proof.
  intros * Hin Hinm.
  pose proof po.(pou_good) as Good.
  induction ((pou_vars po ++ pou_temps po)) as [|(x', t)];
    inv Hinm; inversion_clear Good as [|? ? Valid'].
  - inv Valid'. contradiction.
  - now apply IHl.
Qed.

  Hint Resolve filter_val_filter_In1 filter_val_filter_In2 find_pou_decl2find_pou.

End ST_SYNTAX.


Module ST_SyntaxFun
       (Import Ids   : IDS)
       (Import Op    : ST_OPERATORS)
       (Import OpAux : OPERATORS_AUX Op) <: ST_SYNTAX Ids Op OpAux.
  Include ST_SYNTAX Ids Op OpAux.
End ST_SyntaxFun.