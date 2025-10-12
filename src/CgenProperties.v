From Coq Require Import ZArith.

From compcert Require Import common.Errors.
From compcert Require Import common.Globalenvs.
From compcert Require Import lib.Coqlib.
From compcert Require Import lib.Maps.
From compcert Require Import lib.Integers.
From compcert Require Import cfrontend.Ctypes.
From compcert Require Import cfrontend.Clight.

From Velus Require Import Common.
From Velus Require Import Common.CompCertLib.
From Velus Require Import Ident.
From Velus Require Import Environment.
Require Import Cgen.
Require Import ST_Interface.

Import ST.
Import ST.Syn  .
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z.

(** Properties  *)

Module MProps := FMapFacts.Properties(M).
Import MProps.

Lemma eq_key_equiv:
  forall k x k' x',
    M.eq_key (elt:=ident) (k, x) (k', x') <-> k = k'.
Proof.
  intros (x1, x2) x3 (x'1, x'2) x'3.
  unfold M.eq_key, M.Raw.Proofs.PX.eqk; simpl; split; intro H.
  - destruct H; subst; auto.
  - inv H; split; auto.
Qed.

Lemma setoid_in_key:
  forall l k x,
    SetoidList.InA (M.eq_key (elt:=ident)) (k, x) l <-> InMembers k l.
Proof.
  induction l as [|(k', x')]; split; intros Hin; try inv Hin.
  - constructor.
    now rewrite <-eq_key_equiv with (x:=x) (x':=x').
  - destruct (IHl k x); apply inmembers_cons; auto.
  - constructor.
    now apply eq_key_equiv.
  - destruct (IHl k x); apply SetoidList.InA_cons; right; auto.
Qed.

Lemma eq_key_elt_equiv:
  forall k x k' x',
    M.eq_key_elt (elt:=ident) (k, x) (k', x') <-> (k, x) = (k', x').
Proof.
  intros (x1, x2) x3 (x'1, x'2) x'3.
  unfold M.eq_key_elt, M.Raw.Proofs.PX.eqke; simpl; split; intro H.
  - destruct H as [[]]; subst; auto.
  - inv H; split; auto.
Qed.

Lemma setoid_in_key_elt:
  forall l k x,
    SetoidList.InA (M.eq_key_elt (elt:=ident)) (k, x) l <-> In (k, x) l.
Proof.
  induction l as [|(k', x')]; split; intros Hin; try inv Hin.
  - constructor.
    symmetry; now rewrite <-eq_key_elt_equiv.
  - destruct (IHl k x); apply in_cons; auto.
  - constructor.
    now apply eq_key_elt_equiv.
  - destruct (IHl k x); apply SetoidList.InA_cons; right; auto.
Qed.

Lemma setoid_nodup:
  forall l,
    SetoidList.NoDupA (M.eq_key (elt:=ident)) l <-> NoDupMembers l.
Proof.
  induction l as [|(k, x)]; split; intro Nodup; inv Nodup; constructor.
  - now rewrite <-setoid_in_key with (x:=x).
  - now rewrite <-IHl.
  - now rewrite setoid_in_key.
  - now rewrite IHl.
Qed.

Lemma MapsTo_add_same:
  forall m o f (c c': ident),
    M.MapsTo (o, f) c (M.add (o, f) c' m) ->
    c = c'.
Proof.
  intros * Hin.
  assert (M.E.eq (o, f) (o, f)) as E by reflexivity.
  pose proof (@M.add_1 _ m (o, f) (o, f) c' E) as Hin'.
  apply M.find_1 in Hin; apply M.find_1 in Hin'.
  rewrite Hin in Hin'; inv Hin'; auto.
Qed.

Lemma MapsTo_add_empty:
  forall o f o' f' c c',
    M.MapsTo (o, f) c (M.add (o', f') c' (M.empty ident)) ->
    o = o' /\ f = f' /\ c = c'.
Proof.
  intros * Hin.
  destruct (M.E.eq_dec (o', f') (o, f)) as [[E1 E2]|E1]; simpl in *.
  - subst. repeat split; auto.
    eapply MapsTo_add_same; eauto.
  - apply M.add_3 in Hin; simpl; auto.
    apply M.find_1 in Hin; discriminate.
Qed.


Remark Forall_add:
  forall x y a m P,
    Forall P (M.elements m) ->
    P ((x, y), a) ->
    Forall P (M.elements (elt:=ident) (M.add (x, y) a m)).
Proof.
  intros * Hm H.
  rewrite Forall_forall in *.
  intros ((x', y'), a') Hin.
  apply setoid_in_key_elt, M.elements_2 in Hin.
  destruct (M.E.eq_dec (x, y) (x', y')) as [E|E].
  - destruct E; simpl in *; subst.
    apply MapsTo_add_same in Hin.
    now subst.
  - apply M.add_3 in Hin; auto.
    apply M.elements_1, setoid_in_key_elt in Hin; auto.
Qed.
Remark translate_param_fst:
  forall xs, map fst (map translate_param xs) = map fst xs.
Proof.
  intro; rewrite map_map.
  induction xs as [|(x, t)]; simpl; auto.
  now rewrite IHxs.
Qed.



Lemma NoDupMembers_make_members:
  forall c, NoDupMembers  (mk_members c).
Proof.
  intro; unfold mk_members.

  pose proof (pou_nodup c) as Nodup.
  apply NoDup_app_weaken in Nodup.
  rewrite fst_NoDupMembers.
  rewrite translate_param_fst;eauto.
Qed.
Hint Resolve NoDupMembers_make_members.

Lemma build_check_size_env_ok:
  forall types gvars gvars_vol defs public main p,
    make_program' types gvars gvars_vol defs public main = OK p ->
    build_composite_env types = OK p.(prog_comp_env)
    /\ check_size_env p.(prog_comp_env) types = OK tt.
Proof.
  unfold make_program'; intros.
  destruct (build_composite_env' types) as [[gce ?]|?]; try discriminate.
  destruct (check_size_env gce types) eqn: E; try discriminate.
  destruct u; inv H; simpl; split; auto.
Qed.

Corollary build_ok:
  forall types gvars gvars_vol defs public main p,
    make_program' types gvars gvars_vol defs public main = OK p ->
    build_composite_env types = OK p.(prog_comp_env).
Proof.
  intros * H.
  apply (proj1 (build_check_size_env_ok _ _ _ _ _ _ _ H)).
Qed.

Lemma check_size_ok:
  forall ce types,
    check_size_env ce types = OK tt ->
    Forall (fun t => match t with
                    Composite id _ _ _ => check_size ce id = OK tt
                  end) types.
Proof.
  intros * H.
  induction types as [|(id, su, m, attr) types IH]; auto.
  simpl in H.
  destruct (check_size ce id) eqn: E; try discriminate; destruct u; simpl in H.
  constructor; auto.
Qed.

Lemma type_pres:
  forall po e, Clight.typeof (gen_exp po e) = cltype (typeof e).
Proof.
  induction e ; simpl; auto.
  (* - destruct (is_inst t); auto. *)
  - destruct c; auto. 
  - destruct u; auto.
Qed.
Hint Resolve type_pres.

 Lemma c_objs_field_offset:
  forall ge o c po,
    In (o, c) ( po.(pou_vars)) ->
    exists d, field_offset ge o (mk_members po) = Errors.OK d.
Proof.
  intros * Hin.
  unfold field_offset.
  cut (forall ofs, exists d,
            field_offset_rec ge o (mk_members po) ofs = Errors.OK d); auto.
  unfold mk_members.
  apply in_split in Hin.
  destruct Hin as (ws & xs & Hin).
  rewrite Hin, map_app, map_cons.
  (* rewrite app_assoc. *)
  generalize (map translate_param ws).
  generalize (map translate_param xs).
  clear Hin ws xs.
  intros ws xs.
  induction xs as [|x xs IH]; intros ofs.
  - simpl. setoid_rewrite peq_true. now eexists.
  - destruct x as (x, ty).
    destruct (ident_eq_dec o x) as [He|Hne].
    + simpl. rewrite He, peq_true. now eexists.
    + simpl. rewrite peq_false with (1:=Hne). apply IH.
  Qed. 

Check in_field_type.
Lemma field_translate_obj_type:
  forall prog ponm po id,
    find_pou_decl ponm prog = Some (po) ->
    forall o c,
      In (o, c) (filter_inst po.(pou_vars) ) ->
      (get_pou_name c) = Some id ->
      field_type o (mk_members po) = Errors.OK (type_of_inst id).
Proof.
  intros * Hfind ? ? Hin HN.
  apply in_field_type; auto.
  
  unfold mk_members.
  destruct c; try discriminate.
  inv HN.
  
  apply in_map_iff. exists (o, Tinst id). 
  split;eauto.
  apply filter_In in Hin as (?&?);eauto.
Qed.

Section MethodSpec.
  

  Definition method_spec(po:pou_decl) (fd: function)(stmt: stmt ) : Prop :=
    fd.(fn_params) = [(self, type_of_inst_p po.(pou_name))]
    /\ fd.(fn_return) = Tvoid
    /\ fd.(fn_callconv) = AST.cc_default
    /\ fd.(fn_vars) = []
    /\ fd.(fn_temps) = (mk_members_temp  po)
    /\ list_norepet (var_names fd.(fn_params))
    /\ list_norepet (var_names fd.(fn_vars))
    /\ list_disjoint (var_names fd.(fn_params)) (var_names fd.(fn_temps))
    /\ fd.(fn_body) = (translate_stmt po stmt ) .

  Lemma method_spec_eq:
    forall  po fd1 fd2 st,
      method_spec  po fd1 st->
      method_spec  po fd2 st->
      fd1 = fd2.
  Proof.
    unfold method_spec; destruct fd1, fd2; simpl;
      intros; intuition; f_equal; congruence.
  Qed.

  Variable (po_id po_cid: ident) (po po_c: pou_decl) (pro pro' pro'': project) (fid: ident).
  Hypothesis (Findowner : find_pou po_id pro = Some (po, pro'))
             (Findcl    : find_pou po_cid pro' = Some (po_c, pro''))
             (* (Findmth   : find_method fid c.(c_methods) = Some f) *)
             (WTp       : wt_project pro).

End MethodSpec.


Lemma fun_id_vaild:
valid ID_RESET /\ valid ID_EXEC.
Proof.
    unfold ID_RESET,ID_EXEC.
    unfold fun_id, valid, sep.
    simpl.
    rewrite pos_to_str_equiv.
    rewrite pos_to_str_equiv.
    split.
    intro.
    (* simpl in H. *)
    (* inv H; try discriminate.  *)
    repeat (inv H; try discriminate;inv H0; try discriminate).
    intro.
    (* inv H; try discriminate. *)
    repeat (inv H; try discriminate;inv H0; try discriminate).
Qed.


(* Lemma pou_name2pou_eq :
forall a pro' ,
wt_project (a :: pro') ->
ident_eqb (pou_name a) (pou_name a0) = true ->
a a0. *)

Lemma pree2:
forall pro' a funnm,
wt_project (pro') ->
funnm = ID_RESET \/ funnm = ID_EXEC ->
In (prefix funnm (pou_name a))
  (flat_map
     (fun x0 : pou_decl =>
      [prefix ID_RESET (pou_name x0);
      prefix ID_EXEC (pou_name x0)]) pro') ->
Forall(fun po' : pou_decl => pou_name a <> pou_name po') pro' ->
In a pro' 
.
Proof.
induction pro'.
+
intros. inv H1.
+
intros.
simpl in H1.
destruct(ident_eqb (pou_name a) (pou_name a0) ) eqn:eq.
-
rewrite ident_eqb_eq in eq.
rewrite <- eq in H2.
assert(In a (a::pro')).
{
  simpl.
  eauto. 
}
eapply Forall_forall in H2;eauto.
congruence.
-
destruct H0;destruct H1;subst.
--
eapply prefix_injective in H1;subst; try eapply fun_id_vaild.
destruct H1.
rewrite ident_eqb_neq in eq.
congruence.
--
destruct H1.
---
eapply prefix_injective in H0;subst; try eapply fun_id_vaild.
destruct H0.
rewrite ident_eqb_neq in eq.
congruence.
---
inv H.
eapply IHpro'  in H5.
simpl;eauto.
left.
eauto.
eauto.
inv H2.
eauto.
--
eapply prefix_injective in H1; try eapply fun_id_vaild.
destruct H1.
rewrite ident_eqb_neq in eq.
congruence.
--
destruct H1.
---
eapply prefix_injective in H0; try eapply fun_id_vaild.
destruct H0.
rewrite ident_eqb_neq in eq.
congruence.
---
inv H.
inv H2.
eapply IHpro' in H5;eauto.
simpl;eauto.
Qed.


Section TranslateOk.

  Variable pro: project.
  Variable tprog: Clight.program.

  Let tge := globalenv tprog.
  Let gcenv := genv_cenv tge.

  Hypothesis TRANSL: translate pro = Errors.OK tprog.
  Hypothesis WT: wt_project pro.

  Lemma Consistent:
    composite_env_consistent gcenv.
  Proof.
    unfold translate in  TRANSL.
    destruct (split (map gen_pou pro)) as (s,f) eqn:E; simpl in TRANSL; try discriminate.
apply build_ok in TRANSL.
    eapply build_composite_env_consistent in TRANSL; auto.
  Qed.


(* Lemma pre0: *)

(* Lemma prefix_ *)
Inductive wt_pro_id_list: project -> (list ident) -> Prop :=
 |  pro_po_id_list0:
    wt_pro_id_list [] []
 | pro_po_id_list01:
    forall pl il po0,
    wt_project (po0::pl) ->
    wt_pro_id_list pl il ->
    wt_pro_id_list (po0::pl)  ((prefix ID_RESET (pou_name po0)) :: (prefix ID_EXEC (pou_name po0 ):: il))
.

Lemma wt_fun_eq:
  wt_pro_id_list pro (concat
  (map (fun x0 : pou_decl => [prefix ID_RESET (pou_name x0); prefix ID_EXEC (pou_name x0)]) pro)) .
  Proof.
  clear TRANSL.
  induction pro.
  +
  simpl; try econstructor.
  +
  inv WT.
  assert(WT:wt_project p) by eauto.
  eapply IHp in H2.
  simpl.
  econstructor;eauto.
  econstructor;eauto.
  Qed.
Lemma pree:
forall pro' a funnm,
wt_project pro' ->
In a pro' ->
funnm = ID_RESET \/ funnm = ID_EXEC ->
In (prefix funnm (pou_name a))
  (flat_map
     (fun x0 : pou_decl =>
      [prefix ID_RESET (pou_name x0);
      prefix ID_EXEC (pou_name x0)]) pro') 
.
Proof.
induction pro'.
intros. inv H0.
intros.
simpl.
inv H.
destruct(ident_eqb (pou_name a) (pou_name a0) ) eqn:eq.
-
rewrite ident_eqb_eq in eq.
rewrite eq.
destruct H1;subst;eauto.
-
assert(In a0 pro').
{
  inv H0.
  +assert((pou_name a0) = (pou_name a0)) by eauto.
  rewrite <- ident_eqb_eq in H.
  try congruence.
  + eauto.
}
eapply IHpro' in H;eauto.
Qed.




Lemma prefix_norepet:
  list_norepet 
  (concat
  (map (fun x0 : pou_decl => [prefix ID_RESET (pou_name x0); prefix ID_EXEC (pou_name x0)]) pro))
  .
  Proof.
  clear TRANSL.
  assert(WTTT:  wt_project pro) by eauto.
  rewrite <- flat_map_concat_map.
  induction pro as [|].
  +simpl. econstructor.
  +
    inv WT.
    assert(WTT: wt_project p) by eauto.
    eapply IHp in H2.
    simpl.
    assert(forall A (a:A) b l, a::b::l = [a;b] ++ l).
    {
      intros.
      eauto. 
    }
    rewrite H.
    eapply list_norepet_append;eauto.
    econstructor.
    - intro. 
      inv H0; try congruence.
      --
        unfold ID_EXEC,ID_RESET  in H4.
        eapply prefix_injective in H4.
        ---
        destruct H4.
        eapply pos_of_str_injective in H0.
        inv H0.
        ---
        unfold fun_id, valid, sep.
        intro.
        rewrite pos_to_str_equiv in H0.
        simpl in H0.
        repeat (inv H0; try discriminate;inv H5; try discriminate).
        ---
        unfold fun_id, valid, sep.
        intro.
        rewrite pos_to_str_equiv in H0.
        simpl in H0.
        repeat (inv H0; try discriminate;inv H5; try discriminate).
      --
        inv H4.
    -
    econstructor; try econstructor.
      intro. inv H0.
    -

    eapply list_disjoint_cons_l.
    eapply list_disjoint_cons_l.
    --
    unfold  list_disjoint . eauto.
    --
    intro.
    inv WTTT.
    eapply pree2 in WTT;eauto.
    eapply Forall_forall in H8;eauto.
    --
    intro.
    eapply pree2 with(3:=H0) in WTT;eauto.
    inv WTTT.
    eapply Forall_forall in H8;eauto.
    - eauto. 
  Qed. 



  Lemma prog_defs_norepet:
    list_norepet (map fst (prog_defs tprog)).
  Proof.

    unfold translate, make_program'  in TRANSL.
    destruct (split (map gen_pou pro)) as (s,f) eqn:E; try discriminate.
    destruct (build_composite_env' (concat s) ); try discriminate.
    destruct s0.
    destruct (check_size_env x (concat s)); try discriminate; simpl in TRANSL.
    assert(A: list_norepet(concat (map(fun x0 : pou_decl =>[prefix ID_RESET (pou_name x0);prefix ID_EXEC (pou_name x0)]) pro))).
    {
      eapply prefix_norepet.
    }
    inv TRANSL.
    simpl.
    unfold gen_pou in E.
    eapply split_map in E; destruct E.
    rewrite H0.
    rewrite concat_map.
    rewrite map_map.
    simpl.
    eauto.
  Qed.


  Section ClassProperties.

    Variables (po_name: ident) (po: pou_decl) (pro': project).
    Hypothesis Findcl: find_pou po_name pro = Some (po, pro').
    
    Lemma make_members_co:
      (exists co, gcenv!po_name = Some co
             /\ co_su co = Struct
             /\ co_members co = ( mk_members po)
             /\ attr_alignas (co_attr co) = None
             /\ NoDupMembers (co_members co)
             /\ co.(co_sizeof) <= Ptrofs.max_unsigned).
    Proof.
      unfold translate in TRANSL.
  
      pose proof (find_pou_name' _ _ _ _ Findcl); subst.
      destruct (split (map gen_pou pro)) as (s,f) eqn:E.
      apply build_check_size_env_ok in TRANSL; destruct TRANSL as [? SIZE].
      (*  Ctypes.Composite (pou_name p_decl) Ctypes.Struct _members Ctypes.noattr *)

       assert (In (Composite (pou_name po) Struct ( mk_members po) noattr) (concat s)).
      { unfold gen_pou  in E.
        apply split_map in E.
        destruct E as [Structs].
        unfold mk_members in Structs.
        assert (Findpou': In po pro ). {
          eapply find_pou_decl_In;eauto.
          eapply find_pou2find_pou_decl;eauto.
        }
        apply in_map with (f:=fun p_decl : pou_decl =>[make_struct p_decl])
          in Findpou'.
        apply in_concat' with (l:=[make_struct po] ).
        -  apply in_eq.
        - now rewrite Structs.
      }
      edestruct build_composite_env_charact as (co & Hco & Hmembers & Hattr & ?); eauto.
      exists co; repeat split; auto.
      - rewrite Hattr; auto.
      - rewrite Hmembers. apply NoDupMembers_make_members.
      - eapply check_size_ok, Forall_forall in SIZE; eauto; simpl.
        unfold check_size in SIZE; rewrite Hco in SIZE.
        cases_eqn Le.
        rewrite Zle_is_le_bool; auto.
    Qed. 

    Section MethodProperties.
      Variables (funid: ident) .
      Hypothesis Findmth: funid = ID_EXEC /\ funid = ID_RESET.
    End MethodProperties.

  End ClassProperties.
End TranslateOk.
