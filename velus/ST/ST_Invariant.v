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

From compcert Require Import common.Separation.
From compcert Require Import common.Values.
From compcert Require Import common.Memdata.
From compcert Require Import common.Memory.
From compcert Require Import common.Globalenvs.
From compcert Require common.Errors.
From compcert Require Import cfrontend.Ctypes.
From compcert Require Import cfrontend.Clight.
From compcert Require Import lib.Maps.
From compcert Require Import lib.Coqlib.
From compcert Require Import lib.Integers.

From Velus Require Import Common.
From Velus Require Import Common.CompCertLib.
From Velus Require Import Ident.
From Velus Require Import Environment.
From Velus Require Import VelusMemory.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import ZArith.BinInt.

From Coq Require Import Program.Tactics.

From Velus Require Import ObcToClight.MoreSeparation.
(* From Velus Require Import ObcToClight.Generation. *)
(* From Velus Require Import ObcToClight.GenerationProperties. *)
Require Import Cgen.
Require Import ST_Interface.
Require Import ST.
Import ST.Syn .
Import ST.Sem.
Import ST.Typ.
From Hammer Require Import Hammer Reconstr.
Open Scope list.
Open Scope sep_scope.
Open Scope Z.

Definition match_value (ov: option val) (v: val) : Prop :=
  match ov with
  | None => True
  | Some v' => v = v'
  end.

Definition match_var (ve: venv) (cte: temp_env) (x: ident) : Prop :=
  match cte ! x with
  | Some v => match_value (Env.find x ve) v
  | None => False
  end.

Section Staterep.
  Variable ge : composite_env.
  (**)
    Fixpoint staterep
           (p_decls: list(pou_decl)) (p_name: ident) (me: menv) (b: block) (ofs: Z): massert :=
    match p_decls with
    | nil => sepfalse
    | po :: p' =>
      if ident_eqb p_name po.(pou_name)
      then
        sepall (fun '((x, ty): ident * type) =>
                  match field_offset ge x (mk_members_all  po) with
                  | Errors.OK d =>
                    match  get_pou_name ty with  
                    | Some c =>
                      staterep p' c (instance_match x me) b (ofs + d)
                    | None =>
                      contains_w (type_chunk ty) b (ofs + d) (match_value (find_val x me))
                    end
                  | Errors.Error _ => sepfalse
                  end                             
                  )  po.(pou_vars)
      else staterep p' p_name me b ofs
    end.

    Definition staterep_fun 
      (p_decls: list(pou_decl)) (po: pou_decl) (me: menv) (b: block) (ofs: Z) '((x, ty): ident * type) : massert :=
      match field_offset ge x (mk_members_all  po) with
      | Errors.OK d =>
        match  get_pou_name ty with  
        | Some c =>
          staterep p_decls c (instance_match x me) b (ofs + d)
        | None =>
          contains_w (type_chunk ty) b (ofs + d) (match_value (find_val x me))
        end
      | Errors.Error _ => sepfalse
      end .
  

  Lemma staterep_cons:
    forall po pro p_name me b ofs,
      p_name = po.(pou_name) ->
      staterep (po :: pro) p_name me b ofs <-*->
      sepall (staterep_fun  pro po me b ofs)  po.(pou_vars).
  Proof.
    intros * Hnm.
    apply ident_eqb_eq in Hnm.
    simpl; rewrite Hnm; reflexivity.
  Qed.

  Lemma staterep_skip_cons:
    forall po prog p_name me b ofs,
      p_name <> po.(pou_name) ->
      staterep (po :: prog) p_name me b ofs <-*-> staterep prog p_name me b ofs.
  Proof.
    intros * Hnm.
    apply ident_eqb_neq in Hnm.
    simpl; rewrite Hnm; reflexivity.
  Qed. 

  Lemma staterep_skip_app:
    forall ponm prog oprog me b ofs,
      find_pou ponm oprog = None ->
      staterep (oprog ++ prog) ponm me b ofs <-*-> staterep prog ponm me b ofs.
  Proof.
    intros * Hnin.
    induction oprog as [|po oprog IH].
    - rewrite app_nil_l. reflexivity.
    - apply find_pou_none in Hnin; destruct Hnin.
      rewrite <-app_comm_cons.
      rewrite staterep_skip_cons; auto.
  Qed.

  Remark staterep_skip:
    forall pro pro' pou_name po  me b ofs,
      find_pou pou_name pro = Some (po,pro') ->
      staterep pro pou_name me b ofs <-*->
      staterep (po::pro') pou_name me b ofs.
  Proof.
    intros * Find.
    pose proof (find_pou_app _ _ _ _ Find) as (? & Hprog & FindNone).
    rewrite Hprog.
    rewrite staterep_skip_app; auto.
  Qed.


End Staterep.

(** The struct_in_bounds predicate.

    TODO: add explanatory text. *)

Section StructInBounds.
  Variable env : composite_env.
  Hypothesis env_consistent: composite_env_consistent env.

  Definition struct_in_bounds (min max ofs: Z) (flds: Ctypes.members) :=
    min <= ofs /\ ofs + sizeof_struct env 0 flds <= max.

  Lemma struct_in_bounds_sizeof:
    forall id co,
      env!id = Some co ->
      struct_in_bounds 0 (sizeof_struct env 0 (co_members co)) 0 (co_members co).
  Proof.
    intros. unfold struct_in_bounds. auto with zarith.
  Qed.

  Lemma struct_in_bounds_weaken:
    forall min' max' min max ofs flds,
      struct_in_bounds min max ofs flds ->
      min' <= min ->
      max <= max' ->
      struct_in_bounds min' max' ofs flds.
  Proof.
    unfold struct_in_bounds. destruct 1; intros. auto with zarith.
  Qed.

  Lemma struct_in_bounds_field:
    forall min max ofs flds id d,
      struct_in_bounds min max ofs flds ->
      field_offset env id flds = Errors.OK d ->
      min <= ofs + d <= max.
  Proof.
    unfold struct_in_bounds.
    intros * (Hmin & Hmax) Hfo.
    destruct (field_offset_type _ _ _ _ Hfo) as (ty & Hft).
    destruct (field_offset_in_range _ _ _ _ _ Hfo Hft) as (H0d & Hsize).
    split; auto with zarith.
    apply Z.le_trans with (2:=Hmax).
    apply Z.add_le_mono; auto with zarith.
    apply Z.le_trans with (2:=Hsize).
    rewrite Zplus_0_r_reverse at 1.
    auto using (Z.ge_le _ _ (sizeof_pos env ty)) with zarith.
  Qed.

  Lemma struct_in_struct_in_bounds:
    forall min max ofs flds id sid d co a,
      struct_in_bounds min max ofs flds ->
      field_offset env id flds = Errors.OK d ->
      field_type id flds = Errors.OK (Tstruct sid a) ->
      env!sid = Some co ->
      co_su co = Struct ->
      struct_in_bounds min max (ofs + d) (co_members co).
  Proof.
    unfold struct_in_bounds.
    intros * (Hmin & Hmax) Hfo Hft Henv Hsu.
    apply field_offset_in_range with (1:=Hfo) in Hft.
    destruct Hft as (Hd0 & Hsizeof).
    split; auto with zarith.
    apply Zplus_le_compat_l with (p:=ofs) in Hsizeof.
    apply Z.le_trans with (1:=Hsizeof) in Hmax.
    apply Z.le_trans with (2:=Hmax).
    simpl; rewrite Henv, Z.add_assoc.
    apply Z.add_le_mono_l.
    specialize (env_consistent _ _ Henv).
    rewrite (co_consistent_sizeof _ _ env_consistent), Hsu.
    apply align_le.
    destruct (co_alignof_two_p co) as (n & H2p).
    rewrite H2p.
    apply two_power_nat_pos.
  Qed.

End StructInBounds.

Section StateRepProperties.

  Variable prog: program.
  Variable gcenv: composite_env.

  (* Hypothesis gcenv_consistent: composite_env_consistent gcenv.

  Hypothesis make_members_co:
    forall po_name pro po  ,
      find_pou_decl po_name pro = Some po ->
      (exists co, gcenv!po_name = Some co
             /\ co_su co = Struct
             /\ co_members co = mk_members_all po
             /\ attr_alignas (co_attr co) = None
             /\ NoDupMembers (co_members co)
             /\ co.(co_sizeof) <= Ptrofs.max_unsigned). *)
         
  (* Axiom struct_in_struct_in_bounds':
    forall min max ofs po_name po o c po' pro,
      wt_project pro ->
      find_pou_decl po_name pro = Some po ->
      struct_in_bounds gcenv min max ofs (mk_members_all po) ->
      In (o, c) (map get_id_id  ((filter_inst po.(pou_vars)) ++ (filter_inst po.(pou_temps))) ) ->
      find_pou_decl c pro = Some po' ->
      exists d, field_offset gcenv o (mk_members_all po) = Errors.OK d
           /\ struct_in_bounds gcenv min max (ofs + d) (mk_members_all po'). *)
  (* Proof.
    intros * WTp Hfc Hsb Hin Hfc'.
    destruct (c_objs_field_offset gcenv _ _ _ Hin) as (d & Hfo).
    exists d; split; auto.
    destruct (make_members_co _ _ _ Hfc)
      as (po_co & Hg & Hsu & Hmem & Hattr & Hndup).
    rewrite <-Hmem in *.
    eapply find_class_chained with (1:=WTp) (2:=Hfc) in Hfc'.
    destruct (make_members_co _ _ _ Hfc')
      as (po'_co & Hg' & Hsu' & Hmem' & Hattr' & Hndup').
    rewrite <-Hmem' in *.
    pose proof (field_offset_type _ _ _ _ Hfo) as Hty.
    destruct Hty as (ty & Hty).
    eapply struct_in_struct_in_bounds with (a:=noattr); eauto.
    clear make_members_co.
    (* Show that the field_type is a Tstruct *)
    pose proof po.(c_nodup) as Hnodup.
    rewrite Permutation.Permutation_app_comm in Hnodup.
    assert (~InMembers o po.(c_mems)) as Hnmem.
    { apply In_InMembers in Hin.
      apply NoDup_app_In with (x:=o) in Hnodup.
      now rewrite fst_InMembers; auto.
      now rewrite fst_InMembers in Hin. }
    apply NoDup_app_weaken in Hnodup.
    revert Hnodup Hty Hin. rewrite Hmem. unfold make_members.
    rewrite field_type_skip_app.
    2:now rewrite InMembers_translate_param_idem.
    clear.
    induction po.(c_objs) as [|x xs IH]; [now inversion 1|].
    destruct x as [o' c'].
    destruct (ident_eq_dec o o') as [He|Hne].
    - simpl. rewrite He, peq_true. intros Hnodup ? Hoc.
      destruct Hoc as [Hoc|Hin].
      + injection Hoc; intros R1; rewrite <-R1. reflexivity.
      + inv Hnodup.
        match goal with H:~In _ _ |- _ => contradiction H end.
        apply fst_InMembers. now apply In_InMembers in Hin.
    - simpl; rewrite peq_false; auto.
      intros Hnodup Hft Hin.
      destruct Hin; auto.
      now injection H; intros R1 R2; rewrite <-R1,<-R2 in *; contradiction Hne.
      inv Hnodup; auto.
  Qed. *)

  Hint Resolve Z.divide_trans.

  (* Lemma range_staterep:
    forall b ponm,
      wt_program prog ->
      find_class ponm prog <> None ->
      range_w b 0 (sizeof gcenv (type_of_inst ponm)) -*>
      staterep gcenv prog ponm mempty b 0.
  Proof.
    intros * WTp Hfind.
    (* Weaken the goal for proof by induction. *)
    cut (forall lo,
           (alignof gcenv (type_of_inst ponm) | lo) ->
           massert_imp (range_w b lo (lo + sizeof gcenv (type_of_inst ponm)))
                       (staterep gcenv prog ponm mempty b lo)).
    now intro HH; apply HH; apply Z.divide_0_r.

    (* Setup an induction on prog. *)
    revert ponm Hfind.
    remember prog as prog1.
    assert (WTp' := WTp).
    rewrite Heqprog1 in make_members_co, WTp.
    assert (suffix prog1 prog) as Hsub
        by now rewrite Heqprog1.
    clear (* TRANSL *) Heqprog1.
    induction prog1 as [|po prog' IH]; intros ponm Hfind lo Halign.
    now apply not_None_is_Some in Hfind; destruct Hfind; discriminate.
    inversion_clear WTp' as [|? ? WTc WTp'' Hnodup]; subst.

    (* Staterep looks for the named class: found now or later? *)
    destruct (ident_eqb po.(c_name) ponm) eqn:Hponm.

    - (* Exploit make_members_co for the named class. *)
      apply not_None_is_Some in Hfind.
      destruct Hfind as ((po', prog'') & Hfind).
      assert (find_class ponm prog = Some (po', prog'')) as Hprog
          by apply find_class_sub_same with (1:=Hfind) (2:=WTp) (3:=Hsub).
      destruct (make_members_co _ _ _ Hprog)
        as (co & Hg & Hsu & Hmem & Hattr & Hndup & ?).

      (* find_class succeeds for ponm (deliberately after previous step). *)
      simpl in Hfind. rewrite Hponm in Hfind.
      injection Hfind; intros He1 He2; rewrite <-He1, <-He2 in *.
      clear Hfind He1 He2.

      (* Develop some facts about member alignment. *)
      pose proof (co_members_alignof _ _ (gcenv_consistent _ _ Hg) Hattr)
        as Hcoal.
      rewrite Hmem in Hcoal. unfold make_members in Hcoal.
      apply Forall_app in Hcoal. destruct Hcoal as [Hcoal1 Hcoal2].
      simpl in Halign. rewrite Hg, align_noattr in Halign.
      assert (Hndup':=Hndup). rewrite Hmem in Hndup'.

      (* Massage the goal into two parallel parts: for locals and instances. *)
      simpl. unfold staterep_mems.
      rewrite ident_eqb_sym in Hponm.
      rewrite Hponm, Hg, <-Hmem.
      rewrite split_range_fields
      with (1:=gcenv_consistent) (2:=Hg) (3:=Hsu) (4:=Hndup).
      rewrite Hmem at 2. unfold make_members.
      rewrite sepall_app.
      apply sep_imp'.

      + (* Divide up the memory sub-block for po.(c_mems). *)
        pose proof (field_translate_mem_type _ _ _ _ Hprog) as Htype.
        clear Hcoal2.
        induction po.(c_mems) as [|m ms]; auto.
        apply Forall_cons2 in Hcoal1.
        destruct Hcoal1 as [Hcoal1 Hcoal2].
        apply sep_imp'; auto with datatypes.
        destruct m; simpl.
        destruct (field_offset gcenv i (co_members co)) eqn:Hfo; auto.
        setoid_rewrite Env.gempty.
        rewrite sizeof_translate_chunk; eauto.
        apply range_contains'; auto with mem.
        apply field_offset_aligned with (ty:=cltype t) in Hfo.
        apply Z.divide_add_r; eauto.
        rewrite <-Hmem in Htype. apply Htype; auto with datatypes.

      + (* Divide up the memory sub-block for po.(c_objs). *)
        pose proof (field_translate_obj_type _ _ _ _ Hprog) as Htype.
        rewrite <-Hmem in Htype.
        destruct WTc as [Ho Hm]; clear Hm.
        induction po.(c_objs) as [|o os]; auto.
        simpl. apply sep_imp'.
        2:now inv Ho; apply Forall_cons2 in Hcoal2; intuition.
        apply Forall_forall with (x:=o) in Ho; auto with datatypes.
        destruct o as [o c].
        apply Forall_cons2 in Hcoal2.
        destruct Hcoal2 as [Hcoal2 Hcoal3].
        specialize (Htype o c (in_eq _ _)).
        clear IHos Hcoal1 Hcoal3 os.
        simpl in *.
        destruct (field_offset gcenv o (co_members co)) eqn:Hfo; auto.
        rewrite instance_match_empty.
        specialize (IH WTp'' (suffix_cons _ _ _ Hsub) c Ho (lo + z)%Z).
        apply not_None_is_Some in Ho.
        destruct Ho as ((c' & prog''') & Ho).
        assert (find_class c prog = Some (c', prog''')) as Hcin'
            by apply find_class_sub_same with (1:=Ho) (2:=WTp)
                                              (3:=suffix_cons _ _ _ Hsub).
        destruct (make_members_co _ _ _ Hcin')
          as (co' & Hg' & Hsu' & Hmem' & Hattr' & Hnodup').
        rewrite Hg', align_noattr in *.
        apply IH.
        apply Z.divide_add_r; eauto.
        eapply field_offset_aligned in Hfo; eauto.
        apply Z.divide_trans with (2:=Hfo).
        simpl. rewrite Hg', align_noattr.
        apply Z.divide_refl.
    - simpl in Hfind.
      rewrite Hponm in Hfind.
      specialize (IH WTp'' (suffix_cons _ _ _ Hsub) ponm Hfind lo Halign).
      rewrite ident_eqb_sym in Hponm.
      apply ident_eqb_neq in Hponm.
      rewrite staterep_skip_cons with (1:=Hponm).
      apply IH.
  Qed.
  *) 
  Lemma staterep_deref_mem:
    forall m me po_name  po pro b ofs d x ty v P,
      find_pou_decl po_name pro = Some po ->
      m |= staterep gcenv pro po_name me b ofs ** P ->
      In (x, ty)  ( po.(pou_vars)  ) ->
      is_inst ty = false ->
      find_val x me = Some v ->
      field_offset gcenv x (mk_members_all po)= Errors.OK d ->
      Clight.deref_loc (cltype ty) m b (Ptrofs.repr (ofs + d)) v.
   Proof.
    intros * Find' Hm Hin Hty Hv Hoff.
    assert(Hin': In (x, ty) ( (pou_vars po))) by auto.
    assert(Find: exists po_l, find_pou po_name pro = Some (po,po_l) ) by ( apply find_pou_decl2find_pou;eauto).
    destruct Find as [po_l Find].
    rewrite staterep_skip in Hm; eauto.
    apply sep_proj1 in Hm.
    simpl in Hm. erewrite find_pou_name, ident_eqb_refl in Hm; eauto.
    apply sepall_in in Hin.
    destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm. clear ws xs.
    rewrite Hoff in Hm. clear Hoff.
    assert (get_pou_name ty = None).
    {
      destruct ty;eauto.
      inv Hty. 
    }
    rewrite H in Hm.
    apply loadv_rule in Hm; auto with mem.
    destruct Hm as [v' [Hloadv Hmatch]].
    unfold match_value in Hmatch.
    rewrite Hv in Hmatch; clear Hv.
    rewrite Hmatch in Hloadv; clear Hmatch.
    apply Clight.deref_loc_value with (2:=Hloadv); eauto.
  Qed. 

  Lemma staterep_field_offset:
    forall m me po_name  po pro_l b ofs x ty P,
      find_pou_decl po_name pro_l = Some po ->
      m |= staterep gcenv pro_l po_name me b ofs ** P ->
      In (x, ty)  ( po.(pou_vars)  ) ->
      is_inst ty = false ->
      exists d, field_offset gcenv x (mk_members_all po) = Errors.OK d
           /\ 0 <= ofs + d <= Ptrofs.max_unsigned.
   Proof.
    intros * Find Hm Hin Hty.
    apply find_pou_decl2find_pou in Find.
    destruct Find.
    rewrite staterep_skip in Hm; eauto.
    Opaque sepconj. simpl in Hm. Transparent sepconj.
    apply find_pou2find_pou_decl in H.
    erewrite find_pou_name, ident_eqb_refl in Hm; eauto.
    apply sep_proj1 in Hm.
    apply sepall_in in Hin. destruct Hin as [ws [xs [Hsplit Hin]]].
    rewrite Hin in Hm. clear Hsplit Hin.
    apply sep_proj1 in Hm.
    clear ws xs.
    (* unfold staterep_mems in Hm. *)
    assert (Hty2 : get_pou_name ty = None).
    {
      destruct ty;eauto.
      inv Hty. 
    }
    rewrite Hty2 in Hm. 
    destruct (field_offset gcenv x (mk_members_all po)).
    + exists z; split; auto.
      eapply contains_no_overflow; eauto.
    + contradict Hm.
  Qed. 

  Lemma staterep_field_offset2:
  forall m me po_name  po pro_l b sofs x ty P,
    find_pou_decl po_name pro_l = Some po ->
    m |= staterep gcenv pro_l po_name me b (Ptrofs.unsigned sofs) ** P ->
    In (x, ty)  ( po.(pou_vars)  ) ->
    is_inst ty = true ->
    struct_in_bounds gcenv 0 Ptrofs.max_unsigned (Ptrofs.unsigned sofs) (mk_members_all po)  ->
    exists d, field_offset gcenv x (mk_members_all po) = Errors.OK d
         /\ 0 <= (Ptrofs.unsigned sofs) + d <= Ptrofs.max_unsigned.
 Proof.
  intros * Find Hm Hin Hty HB.
  apply find_pou_decl2find_pou in Find.
  destruct Find.
  rewrite staterep_skip in Hm; eauto.
   simpl in Hm. 
  apply find_pou2find_pou_decl in H.
  erewrite find_pou_name, ident_eqb_refl in Hm; eauto.
  apply sep_proj1 in Hm.
  apply sepall_in in Hin; destruct Hin as [ws [xs [Hsplit Hin]]].
  rewrite Hin in Hm. clear Hsplit Hin.
  apply sep_proj1 in Hm.
  clear ws xs.
  (* unfold staterep_mems in Hm. *)
  destruct (field_offset gcenv x (mk_members_all po))  eqn:H11 .
  + 
   exists z; split; auto.
   eapply struct_in_bounds_field in HB; eauto.
  + destruct (get_pou_name ty);    contradict Hm.
Qed. 

 (* Lemma sdsd:
forall pro po pro_l' i c' ,
wt_pou_depo pro (po :: pro_l') ->
In (i, Tinst c') (filter_inst (pou_vars po))
-> c' <>  pou_name po
.
Proof.
intros * WT Win .
eapply wt_program_not_same_name with (ty := Tinst c') in WT; eauto.
simpl in WT.
unfold not. intros.
subst.
contradiction.
Qed.  *)

 
    Lemma staterep_extract:
    forall   me b ofs m i po_name' po  P pro_l pro_l' pro pou_name,
      wt_pou_decls pro pro_l ->
      find_pou pou_name pro_l = Some (po,pro_l') ->
      (In (i,Tinst po_name')  po.(pou_vars) /\
      m |= staterep gcenv pro_l pou_name me b ofs ** P)
      -> exists  d,
           field_offset gcenv i (mk_members_all po) = Errors.OK d
          /\ m |= staterep gcenv pro_l po_name' (instance_match i me) b (ofs + d)
                  ** P.
  Proof.
    intros * WT Find .
    intros (Hin & Hmem).
    pose proof Find as Fcid;apply find_pou_name' in Fcid; subst.
    rewrite staterep_skip in Hmem ;eauto.
    rewrite staterep_cons in Hmem ;eauto.
    (* rewrite staterep_skip, staterep_cons, sep_assoc; eauto. *)
    apply sepall_in in Hin as (objs & objs' & E & Hp).
    rewrite Hp in Hmem.
    rewrite sep_assoc in Hmem.
    rewrite sep_drop2 in Hmem.
    unfold staterep_fun  in Hmem.
    (* simpl in Hmem. *)
    (* simpl . *)
    destruct (field_offset gcenv i (mk_members_all  po)) as [d|].
  
    + exists d. intuition;eauto.
      simpl in Hmem.
      inv Hmem;eauto.
    (* + inv Hmem. inv H. *)

    Admitted.

End StateRepProperties.




Definition varsrep (po: pou_decl) (ve: venv) (cte: temp_env) : massert :=
  pure (Forall (match_var ve cte) (map fst (filter_val po.(pou_temps)))).

Lemma varsrep_any_empty:
  forall f ve cte,
    varsrep f ve cte -*> varsrep f vempty cte.
Proof.
  intros.
  apply pure_imp; intro H.
  induction (map fst (filter_val (pou_temps f))) as [|x]; auto.
  inv H; constructor; auto.
  unfold match_var in *; destruct (cte ! x); try contradiction.
  unfold find_val;rewrite Env.gempty.
  constructor.  
Qed.


Lemma varsrep_add:
  forall f ve cte x v,
    varsrep f ve cte -*> varsrep f (Env.add x v ve) (PTree.set x v cte).
Proof.
  intros.
  unfold varsrep.
  rewrite pure_imp.
  intro Hforall.
  induction(filter_val (pou_temps f)) as [|(x', t')]; simpl in *; auto.
  inv Hforall.
  unfold match_var in *.
  constructor.
  - destruct (ident_eqb x' x) eqn: Eq.
    + apply ident_eqb_eq in Eq.
      subst x'.
      rewrite PTree.gss.
      unfold match_value.
      now rewrite Env.gss.
    + apply ident_eqb_neq in Eq.
      rewrite PTree.gso; auto.
      now rewrite Env.gso.
  - now apply IHl.
Qed.

(* Lemma varsrep_add':
  forall f ve cte x v y v',
    ~ InMembers y (pou_temp f) ->
    varsrep f ve cte -*> varsrep f (Env.add x v ve) (PTree.set x v (PTree.set y v' cte)).
Proof.
  intros * Notin.
  transitivity (varsrep f ve (PTree.set y v' cte)).
  - unfold varsrep.
    rewrite pure_imp.
    intro Hforall.
    induction (pou_temp f) as [|(x', t')]; simpl in *; auto.
    inv Hforall.
    apply Decidable.not_or in Notin; destruct Notin.
    unfold match_var in *.
    constructor.
    + rewrite PTree.gso; auto.
    + now apply IHl.
  - apply varsrep_add.
Qed.

Lemma varsrep_add'':
  forall f ve cte x v y v',
    ~ InMembers y (pou_temp f) ->
    x <> y ->
    varsrep f (Env.add x v ve) cte -*> varsrep f (Env.add x v ve) (PTree.set y v' cte).
Proof.
  intros * Notin ?.
  unfold varsrep.
  rewrite pure_imp.
  intro Hforall.
  induction (pou_temp f) as [|(x', t')]; simpl in *; auto.
  inv Hforall.
  apply Decidable.not_or in Notin; destruct Notin.
  unfold match_var in *.
  constructor.
  - rewrite PTree.gso; auto.
  - now apply IHl.
Qed. *)

Lemma varsrep_add''':
  forall f ve cte x v,
    ~ InMembers x (filter_val (pou_temps f)) ->
    varsrep f ve cte -*> varsrep f ve (PTree.set x v cte).
Proof.
  intros * Notin.
  unfold varsrep.
  rewrite pure_imp.
  intro Hforall.
  induction (filter_val (pou_temps f))  as [|(x', t')]; simpl in *; auto.
  inv Hforall.
  apply Decidable.not_or in Notin; destruct Notin.
  unfold match_var in *.
  constructor.
  - rewrite PTree.gso; auto.
  - now apply IHl.
Qed.

Definition var_ptr (b: block) : val :=
  Vptr b Ptrofs.zero.

Section MatchStates.

  Variable ge : composite_env.


  Definition prefix_out_env (e: Clight.env) : Prop :=
    forall x b t,
      e ! x = Some (b, t) ->
      exists o f, x = prefix_out o f.

  Definition bounded_struct_of_class (po: pou_decl) (sofs: ptrofs) : Prop :=
    struct_in_bounds ge 0 Ptrofs.max_unsigned (Ptrofs.unsigned sofs) (mk_members_all  po ) .

  Lemma bounded_struct_of_class_ge0:
    forall c sofs,
      bounded_struct_of_class c sofs ->
      0 <= Ptrofs.unsigned sofs.
  Proof.
    unfold bounded_struct_of_class, struct_in_bounds; tauto.
  Qed.
  Hint Resolve bounded_struct_of_class_ge0.
  Definition selfrep (pro: project) (po: pou_decl) (me: menv) (cte: Clight.temp_env) (sb: block) (sofs: ptrofs) : massert :=
    pure (cte ! self = Some (Vptr sb sofs))
    ** pure (bounded_struct_of_class po sofs)
    ** staterep ge pro po.(pou_name) me sb (Ptrofs.unsigned sofs).

  Lemma selfrep_conj:
    forall m pro po me cte sb sofs P,
      m |= selfrep pro po me cte sb sofs ** P
      <-> m |= staterep ge pro po.(pou_name) me sb (Ptrofs.unsigned sofs) ** P
        /\ cte ! self = Some (Vptr sb sofs)
        /\ bounded_struct_of_class po sofs.
  Proof.
    unfold selfrep; split; intros * H.
    - repeat rewrite sep_assoc in H; repeat rewrite sep_pure in H; tauto.
    - repeat rewrite sep_assoc; repeat rewrite sep_pure; tauto.
  Qed.

Print selfrep.
  Definition match_states
              (pro: project) (po: pou_decl)  '((me, ve): menv * venv)
             '((e, cte): Clight.env * Clight.temp_env)
             (sb: block) (sofs: ptrofs) : massert :=
    pure (wt_state pro me ve po )**
    selfrep pro po me cte sb sofs **
    varsrep po ve cte.

    Lemma match_states_conj:
    forall pro po  me ve e cte m sb sofs  P,
      m |= match_states pro po  (me, ve) (e, cte) sb sofs  ** P <->
      m |= staterep ge pro po.(pou_name) me sb (Ptrofs.unsigned sofs)
           ** varsrep po ve cte
           ** P
      /\ bounded_struct_of_class po sofs
      /\ wt_state pro me ve po
      /\ cte ! self = Some (Vptr sb sofs).
  Proof.
    unfold match_states, selfrep; split; intros * H.
    - repeat rewrite sep_assoc in H; repeat rewrite sep_pure in H.
      tauto.
    - repeat rewrite sep_assoc; repeat rewrite sep_pure.
      tauto.
  Qed.  

  Check wt_state.
  Check match_states.
  (* Lemma match_states_wt_state:
  forall pro c f me ve e cte m sb sofs outb_co P,
    m |= match_states pro c f (me, ve) (e, cte) sb sofs outb_co ** P ->
    wt_state pro me ve c (meth_vars f). *)
  Lemma match_states_wt_state:
    forall pro c  me ve e cte m sb sofs  P,
      m |= match_states pro c  (me, ve) (e, cte) sb sofs  ** P ->
      wt_state pro me ve c .
  Proof.
    setoid_rewrite match_states_conj; tauto.
  Qed. 

  Section MatchStatesPreservation.

    (*****************************************************************)
    (** various basic 'Hoare triples' for memory assignments        **)
    (*****************************************************************)

    Variable
      (** ST program  *)
      (pro     : project)

      (** ST pou *)
      (ownerid  : ident)     (po : pou_decl)     (pro' : project)

      (** ST state *)
      (me       : menv)      (ve     : venv)

      (** Clight state *)
      (m        : Mem.mem)   (e      : Clight.env) (cte   : temp_env)

      (** Clight self structure *)
      (sb       : block)     (sofs   : ptrofs)

      (** Clight output structure *)
      (outb_co  : option (block * composite))

      (** frame *)
      (P        : massert).
Check find_pou.
    Hypothesis (Findcl      : find_pou ownerid pro = Some (po, pro')).

    Variable (v : val) (x : ident) (ty : type).

    Hypothesis (WTv : wt_val v ty).

    (* Lemma outputrep_assign_gt1_mem:
      In (x, ty) caller.(m_out) ->
      (1 < length (m_out caller))%nat ->
      m |= outputrep po caller ve cte outb_co ** P ->
      exists m' b co d,
        outb_co = Some (b, co)
        /\ field_offset ge x (co_members co) = Errors.OK d
        /\ Clight.assign_loc ge (cltype ty) m b (Ptrofs.repr d) v m'
        /\ m' |= outputrep po caller (Env.add x v ve) cte outb_co ** P.
    Proof.
      intros * Hin Len Hmem.
      apply outputrep_notnil in Hmem as (b & co & Hout & Hrep &?& Hco); auto.
      erewrite find_class_name, find_method_name in Hco; eauto.
      apply in_map with (f:=translate_param) in Hin.
      erewrite OutputMatch in Hin; eauto.
      pose proof (m_nodupvars caller) as Nodup.

      (* get the updated memory *)
      apply sepall_in in Hin as [ws [ys [Hys Heq]]].
      unfold fieldsrep in Hrep.
      Local Opaque sepconj match_states.
      rewrite Heq in Hrep; simpl in *.
      destruct (field_offset ge x (co_members co)) as [d|] eqn: Hofs; rewrite sep_assoc in Hrep;
        try (destruct Hrep; contradiction).
      rewrite cltype_access_by_value in Hrep.
      eapply Separation.storev_rule' with (v:=v) in Hrep as (m' & ? & Hrep); eauto with mem.
      exists m', b, co, d; intuition; eauto using assign_loc.
      rewrite outputrep_notnil; auto.
      erewrite find_class_name, find_method_name; eauto.
      exists b, co; split; intuition.
      unfold fieldsrep, fieldrep.
      rewrite Heq, Hofs, cltype_access_by_value, sep_assoc.
      eapply sep_imp; eauto.
      - unfold hasvalue, match_value; simpl.
        rewrite Env.gss.
        now rewrite <-wt_val_load_result.
      - apply sep_imp'; auto.
        do 2 apply NoDupMembers_app_r in Nodup.
        rewrite fst_NoDupMembers, <-translate_param_fst, <-fst_NoDupMembers in Nodup; auto.
        erewrite OutputMatch, Hys in Nodup; auto.
        apply NoDupMembers_app_cons in Nodup.
        destruct Nodup as (Notin & Nodup).
        rewrite sepall_swapp; eauto.
        intros (x' & t') Hin.
        rewrite Env.gso; auto.
        intro; subst x'.
        apply Notin.
        eapply In_InMembers; eauto.
    Qed.

    Lemma outputrep_assign_singleton_mem:
      m_out caller = [(x, ty)] ->
      outputrep po caller ve cte outb_co -*>
      outputrep po caller (Env.add x v ve) (PTree.set x v cte) outb_co.
    Proof.
      intros Eq.
      unfold outputrep, case_out; rewrite Eq.
      unfold match_var; now rewrite PTree.gss, Env.gss.
    Qed.

    Lemma outputrep_assign_var_mem:
      ~ InMembers x (m_out caller) ->
      In (x, ty) (meth_vars caller) ->
      m |= outputrep po caller ve cte outb_co ** P ->
      m |= outputrep po caller (Env.add x v ve) (PTree.set x v cte) outb_co ** P.
    Proof.
      intros * Hnin Hin Hmem.
      eapply sep_imp; eauto.
      unfold outputrep, case_out in *; destruct_list (m_out caller) as (?, ?) (?, ?) ? : Hout; auto.
      - apply pure_imp.
        assert (i <> x) by (intro; subst; apply Hnin; constructor; auto).
        unfold match_var; now rewrite PTree.gso, Env.gso.
      - erewrite find_class_name, find_method_name in*; eauto.
        destruct outb_co as [(outb, outco)|]; auto.
        repeat apply sep_imp'; auto.
        + apply pure_imp.
          rewrite PTree.gso; auto.
          intro; subst; apply (m_notreserved out caller).
          * right; constructor; auto.
          * eapply In_InMembers; eauto.
        + rewrite 2 sep_assoc, 2 sep_pure in Hmem.
          destruct Hmem as (?&?&?).
          eapply fieldsrep_add; eauto.
          erewrite <-OutputMatch; eauto; try (simpl; omega).
          rewrite InMembers_translate_param_idem; auto.
    Qed. *)

    Lemma match_states_assign_state_mem:
      m |= match_states pro po  (me, ve) (e, cte) sb sofs
           ** P ->
      In (x, ty) ( po.(pou_vars)) ->
      is_inst ty = false ->
      exists m' d,
        field_offset ge x (mk_members_all po) = Errors.OK d
        /\ Clight.assign_loc ge (cltype ty) m sb (Ptrofs.repr (Ptrofs.unsigned sofs + d)) v m'
        /\ m' |= match_states pro po  (add_val x v me, ve) (e, cte) sb sofs
                ** P.
    Proof.
      intros Hmem Hin Hty.
      apply match_states_conj in Hmem as (Hmem & ?&?&?).
      erewrite find_pou_name' in Hmem; eauto.

      (* get the updated memory *)
      pose proof Hin.
      apply sepall_in in Hin as [ws [ys [Hys Heq]]].
      rewrite staterep_skip in Hmem; eauto.
      simpl staterep in Hmem; erewrite find_pou_name' in Hmem; eauto.
      (* unfold staterep_mems in Hmem. *)
      rewrite ident_eqb_refl, Heq in Hmem.
      rewrite sep_assoc in Hmem.
      (* apply sep_drop2 in Hmem. *)
      destruct (field_offset ge x (mk_members_all po)) as [d|] eqn: Hofs;try (destruct Hmem; contradiction).

      assert (Hty1: get_pou_name ty = None) by (destruct ty;eauto;inv Hty).
      rewrite Hty1 in Hmem.
      
      eapply Separation.storev_rule' with (v:=v) in Hmem as (m' & ? & Hmem);
        eauto with mem.
      exists m', d; intuition; eauto using assign_loc.
      apply match_states_conj; intuition; eauto.
      erewrite find_pou_name', staterep_skip; eauto.
      simpl staterep .
      erewrite find_pou_name', ident_eqb_refl, Heq, Hofs; eauto.
      rewrite Hty1.
      apply sep_assoc.

      eapply sep_imp. eauto.
      - unfold hasvalue'.
        rewrite find_val_gss.
        now rewrite <-wt_val_load_result.
      - repeat apply sep_imp'; auto.
        pose proof (pou_nodup_vars po) as Nodup.
        assert(Nodup': NoDupMembers (filter_val  (pou_vars po)) ).
        {
          eapply NoDupMembers_filter;eauto.
        }
        rewrite Hys in Nodup.
        apply NoDupMembers_app_cons in Nodup.
        destruct Nodup as (Notin & Nodup).
        (* destruct Nodup. *)
        rewrite sepall_swapp; eauto.
        intros (x' & t') Hin.
        rewrite find_val_gso; auto.
        intro; subst x'.
        apply Notin.
        eapply In_InMembers; eauto.
    Qed.

  End MatchStatesPreservation.

End MatchStates.

(*
Section FunctionEntry.

  (*****************************************************************)
  (** results about allocation of the environment and temporary   **)
  (** environment at function entry                               **)
  (*****************************************************************)

  (* Variable ge: genv. *)
  (* Let gcenv := Clight.genv_cenv ge. *)

  (* Hypothesis Consistent : composite_env_consistent gcenv. *)

  Remark bind_parameter_temps_exists:
    forall xs s ts o to ys vs sptr optr,
      s <> o ->
      NoDupMembers xs ->
      ~ InMembers s xs ->
      ~ InMembers o xs ->
      ~ InMembers s ys ->
      ~ InMembers o ys ->
      length xs = length vs ->
      exists cte',
        bind_parameter_temps ((s, ts) :: (o, to) :: xs)
                             (sptr :: optr :: vs)
                             (create_undef_temps ys) = Some cte'
        /\ Forall (match_var (Env.adds (map fst xs) vs vempty) cte') (map fst (xs ++ ys)).
  Proof.
    unfold match_var.
    induction xs as [|(x, ty)]; destruct vs;
      intros * Hso Nodup Nos Noo Nos' Noo' Hlengths; try discriminate.
    - simpl; econstructor; split; auto.
      unfold match_value, Env.adds; simpl.
      induction ys as [|(y, t)]; simpl; auto.
      assert (y <> s) by (intro; subst; apply Nos'; apply inmembers_eq).
      assert (y <> o) by (intro; subst; apply Noo'; apply inmembers_eq).
      constructor.
      + rewrite Env.gempty.
        do 2 (rewrite PTree.gso; auto).
        now rewrite PTree.gss.
      + apply NotInMembers_cons in Nos'; destruct Nos' as [Nos'].
        apply NotInMembers_cons in Noo'; destruct Noo' as [Noo'].
        specialize (IHys Nos' Noo').
        eapply Forall_impl_In; eauto; simpl.
        intros y' Hin Hmatch.
        assert (y' <> s) by (intro; subst; apply Nos'; eapply fst_InMembers; eauto).
        assert (y' <> o) by (intro; subst; apply Noo'; eapply fst_InMembers; eauto).
        rewrite 2 PTree.gso in *; auto.
        destruct (ident_eqb y' y) eqn: E.
        * apply ident_eqb_eq in E; subst y'.
          rewrite PTree.gss.
          now rewrite Env.gempty.
        * apply ident_eqb_neq in E.
          rewrite PTree.gso; auto.
    - inv Hlengths; inv Nodup.
      edestruct IHxs with (s:=s) (ts:=ts) (o:=o) (to:=to) (sptr:=sptr) (optr:=optr)
        as (cte' & Bind & ?); eauto.
      + eapply NotInMembers_cons; eauto.
      + eapply NotInMembers_cons; eauto.
      + assert (x <> s) by (intro; subst; apply Nos; apply inmembers_eq).
        assert (x <> o) by (intro; subst; apply Noo; apply inmembers_eq).
        exists (PTree.set x v cte'); split.
        * rewrite bind_parameter_temps_comm; auto.
          apply bind_parameter_temps_cons; auto.
          simpl; intros [|[|]]; auto.
        *{ rewrite <-app_comm_cons.
           constructor.
           - rewrite PTree.gss.
             unfold match_value; simpl; rewrite Env.find_gsss; auto.
             now rewrite <-fst_InMembers.
           - eapply Forall_impl_In; eauto; simpl.
             intros x' Hin MV.
             destruct (ident_eqb x' x) eqn: E.
             + rewrite ident_eqb_eq in E; subst x'.
               rewrite PTree.gss; unfold match_value; simpl; rewrite Env.find_gsss; auto.
               now rewrite <-fst_InMembers.
             + rewrite ident_eqb_neq in E.
               rewrite PTree.gso; auto.
               destruct cte' ! x'; try contradiction.
               unfold match_value in *; simpl.
               rewrite Env.find_gsso; auto.
         }
  Qed.

  Remark bind_parameter_temps_exists_noout:
    forall xs s ts ys vs sptr,
      NoDupMembers xs ->
      ~ InMembers s xs ->
      ~ InMembers s ys ->
      length xs = length vs ->
      exists cte',
        bind_parameter_temps ((s, ts) :: xs)
                             (sptr :: vs)
                             (create_undef_temps ys) = Some cte'
        /\ Forall (match_var (Env.adds (map fst xs) vs vempty) cte') (map fst (xs ++ ys)).
  Proof.
    unfold match_var.
    induction xs as [|(x, ty)]; destruct vs;
      intros * Nodup Nos Nos' Hlengths; try discriminate.
    - simpl; econstructor; split; auto.
      unfold match_value, Env.adds; simpl.
      induction ys as [|(y, t)]; simpl; auto.
      assert (y <> s) by (intro; subst; apply Nos'; apply inmembers_eq).
      constructor.
      + rewrite Env.gempty, PTree.gso, PTree.gss; auto.
      + apply NotInMembers_cons in Nos'; destruct Nos' as [Nos'].
        specialize (IHys Nos').
        eapply Forall_impl_In; eauto; simpl.
        intros y' Hin Hmatch.
        assert (y' <> s) by (intro; subst; apply Nos'; eapply fst_InMembers; eauto).
        rewrite PTree.gso in *; auto.
        destruct (ident_eqb y' y) eqn: E.
        * apply ident_eqb_eq in E; subst y'.
          rewrite PTree.gss.
          now rewrite Env.gempty.
        * apply ident_eqb_neq in E.
          now rewrite PTree.gso.
    - inv Hlengths; inv Nodup.
      edestruct IHxs with (s:=s) (ts:=ts) (sptr:=sptr)
        as (cte' & Bind & ?); eauto.
      + eapply NotInMembers_cons; eauto.
      + assert (x <> s) by (intro; subst; apply Nos; apply inmembers_eq).
        exists (PTree.set x v cte'); split.
        * rewrite bind_parameter_temps_comm_noout; auto.
          apply bind_parameter_temps_cons; auto.
          simpl; intros [|]; auto.
        *{ rewrite <-app_comm_cons.
           constructor.
           - rewrite PTree.gss.
             simpl.
             unfold match_value; rewrite Env.find_gsss; auto.
             rewrite <-fst_InMembers; auto.
           - eapply Forall_impl_In; eauto; simpl.
             intros x' Hin MV.
             destruct (ident_eqb x' x) eqn: E.
             + rewrite ident_eqb_eq in E; subst x'.
               rewrite PTree.gss; unfold match_value; simpl.
               rewrite Env.find_gsss; auto.
               rewrite <-fst_InMembers; auto.
             + rewrite ident_eqb_neq in E.
               rewrite PTree.gso.
               destruct cte' ! x'; try contradiction.
               unfold match_value; simpl; rewrite Env.find_gsso; auto.
               auto.
         }
  Qed.

  Remark alloc_mem_vars:
    forall ge vars e m e' m' P,
      let gcenv := Clight.genv_cenv ge in
      m |= P ->
      NoDupMembers vars ->
      Forall (fun xt => sizeof gcenv (snd xt) <= Ptrofs.max_unsigned) vars ->
      alloc_variables ge e m vars e' m' ->
      m' |= sepall (range_inst_env gcenv e') (var_names vars) ** P.
  Proof.
    induction vars as [|(y, t)];
      intros * Hrep Nodup Forall Alloc;
      inv Alloc; subst; simpl.
    - now rewrite <-sepemp_left.
    - inv Nodup; inv Forall.
      unfold range_inst_env at 1.
      erewrite alloc_implies; eauto.
      rewrite sep_assoc, sep_swap.
      eapply IHvars; eauto.
      eapply alloc_rule; eauto; try omega.
      etransitivity; eauto.
      unfold Ptrofs.max_unsigned; omega.
  Qed.

  Lemma alloc_result:
    forall ge f m P,
      let vars := instance_methods f in
      let gcenv := Clight.genv_cenv ge in
      composite_env_consistent ge ->
      Forall (fun xt => sizeof ge (snd xt) <= Ptrofs.max_unsigned /\ wf_struct gcenv xt)
             (make_out_vars vars) ->
      NoDupMembers (make_out_vars vars) ->
      m |= P ->
      exists e' m',
        alloc_variables ge empty_env m (make_out_vars vars) e' m'
        /\ prefix_out_env e'
        /\ m' |= subrep gcenv f e'
               ** (subrep gcenv f e' -* subrep_range gcenv e')
               ** P.
  Proof.
    intros * Consistent Hforall Nodup Hrep; subst.
    rewrite <-Forall_Forall' in Hforall; destruct Hforall.
    pose proof (alloc_exists ge _ empty_env m Nodup) as (e' & m' & Alloc).
    eapply alloc_mem_vars in Hrep; eauto.
    pose proof Alloc as Perm.
    apply alloc_permutation in Perm; auto.
    exists e', m'; split; [auto|split].
    - intros ??? Hget.
      apply PTree.elements_correct in Hget.
      apply in_map with (f:=drop_block) in Hget.
      apply Permutation.Permutation_sym in Perm.
      rewrite Perm in Hget.
      unfold make_out_vars in Hget; simpl in Hget.
      apply in_map_iff in Hget.
      destruct Hget as (((o, f'), c) & Eq & Hget).
      inv Eq. now exists o, f'.
    - pose proof Perm as Perm_fst.
      apply Permutation_fst in Perm_fst.
      rewrite map_fst_drop_block in Perm_fst.
      rewrite Perm_fst in Hrep.
      rewrite <-subrep_range_eqv in Hrep.
      repeat rewrite subrep_eqv; auto.
      rewrite range_wand_equiv in Hrep; eauto.
      + now rewrite sep_assoc in Hrep.
      + eapply Permutation_Forall; eauto.
      + eapply alloc_nodupmembers; eauto.
        * unfold PTree.elements; simpl; constructor.
        * unfold PTree.elements; simpl.
          clear H H0 Nodup Alloc Perm Perm_fst.
          induction (make_out_vars vars); constructor; auto.
        * intros * Hin.
          unfold PTree.elements in Hin; simpl in Hin.
          contradiction.
  Qed.

  (*****************************************************************)
  (** 'Hoare triple' for function entry, depending on the number  **)
  (** of outputs (and inputs, consequently):                      **)
  (**   0 and 1: no 'out' pointer parameter, we only need         **)
  (**            staterep for the sub-state, and we get           **)
  (**            match_states in the callee                       **)
  (**   1 < n  : 'out' pointer parameter, we need both            **)
  (**            staterep for the sub-state and fieldsrep for the **)
  (**            output structure, we get match_states in the     **)
  (**            callee                                           **)
  (*****************************************************************)

  Variable (main_node  : ident)
           (prog       : program)
           (tprog      : Clight.program)
           (do_sync    : bool)
           (all_public : bool).
  Let tge              := Clight.globalenv tprog.
  Let gcenv            := Clight.genv_cenv tge.

  Hypothesis (TRANSL : translate do_sync all_public main_node prog = Errors.OK tprog)
             (WT     : wt_program prog).

  Lemma function_entry_match_states:
    forall cid c prog' fid f fd me vs,
      method_spec c f prog fd ->
      find_class cid prog = Some (c, prog') ->
      find_method fid c.(c_methods) = Some f ->
      wt_mem me prog c ->
      Forall2 (fun v xt => wt_val v (snd xt)) vs (m_in f) ->
      case_out f
               (forall m sb sofs P,
                   bounded_struct_of_class gcenv c sofs ->
                   m |= staterep gcenv prog cid me sb (Ptrofs.unsigned sofs) ** P ->
                   exists e_f le_f m_f,
                     function_entry2 tge fd (Vptr sb sofs :: vs) m e_f le_f m_f
                     /\ m_f |= match_states gcenv prog c f (me, Env.adds (map fst f.(m_in)) vs vempty) (e_f, le_f) sb sofs None
                              ** P)
               (fun _ _ =>
                  forall m sb sofs P,
                    bounded_struct_of_class gcenv c sofs ->
                    m |= staterep gcenv prog cid me sb (Ptrofs.unsigned sofs) ** P ->
                    exists e_f le_f m_f,
                      function_entry2 tge fd (Vptr sb sofs :: vs) m e_f le_f m_f
                      /\ m_f |= match_states gcenv prog c f (me, Env.adds (map fst f.(m_in)) vs vempty) (e_f, le_f) sb sofs None
                               ** P)
               (fun _ =>
                  forall m sb sofs instb instco P,
                   bounded_struct_of_class gcenv c sofs ->
                   m |= staterep gcenv prog cid me sb (Ptrofs.unsigned sofs)
                        ** fieldsrep gcenv vempty (co_members instco) instb
                        ** P ->
                   gcenv ! (prefix_fun cid fid) = Some instco ->
                   exists e_f le_f m_f,
                     function_entry2 tge fd (Vptr sb sofs :: var_ptr instb :: vs) m e_f le_f m_f
                     /\ m_f |= match_states gcenv prog c f (me, Env.adds (map fst f.(m_in)) vs vempty) (e_f, le_f) sb sofs
                                (Some (instb, instco))
                              ** P).
  Proof.
    intros * Spec Findcl Findmth WTmem WTvs.

    assert (NoDupMembers (make_out_vars (instance_methods f)))
      by (eapply NoDupMembers_make_out_vars; eauto; eapply wt_program_find_class; eauto).
    assert (Forall (fun xt => sizeof tge (snd xt) <= Ptrofs.max_unsigned /\ wf_struct gcenv xt)
                   (make_out_vars (instance_methods f)))
      by (eapply instance_methods_caract; eauto).
    assert (Datatypes.length (map translate_param (m_in f)) = Datatypes.length vs)
      by (symmetry; rewrite map_length; eapply Forall2_length; eauto).
    assert (wt_state prog me vempty c (meth_vars f)) by (split; eauto).
    assert (NoDup (map fst (m_in f))) by (apply fst_NoDupMembers, m_nodupin).
    assert (Forall2 (fun y xt => In (y, snd xt) (meth_vars f)) (map fst (m_in f)) (m_in f))
      by (apply Forall2_map_1, Forall2_same, Forall_forall; intros (x, t) Hin; simpl; apply in_app; auto).

    unfold method_spec, case_out in *.
    subst gcenv tge.
    destruct_list (m_out f) as (a,ta) (?,?) ? : Hout; simpl in Spec;
      destruct Spec as (P_f &?&?&?& T_f &?&?&?&?); intros * ? Hmem; try intros Hinstco.

    (* no output *)
    - (* get the allocated environment and memory *)
      edestruct alloc_result as (e_f & m_f &?&?&?); eauto.

      (* get the temporaries *)
      edestruct
        (bind_parameter_temps_exists_noout (map translate_param f.(m_in))
                                           self (type_of_inst_p (pou_name c))
                                           (make_out_temps (instance_methods_temp (rev prog) f)
                                                           ++ map translate_param (m_vars f))
                                           vs (Vptr sb sofs)) as (le_f & Bind & Vars); eauto.
      assert (le_f ! self = Some (Vptr sb sofs))
        by (eapply bind_parameter_temps_implies in Bind; eauto).
      setoid_rewrite <-P_f in Bind.

      exists e_f, le_f, m_f; split.
      + constructor; auto; try congruence.
      + apply match_states_conj; intuition; eauto using m_nodupvars.
        erewrite find_class_name; eauto.
        rewrite sep_swap, outputrep_nil, <-sepemp_left, sep_swap, sep_swap23,
        sep_swap34, sep_swap23, sep_swap; auto.
        apply sep_pure; split; auto.
        repeat rewrite map_app in *.
        repeat rewrite translate_param_fst in Vars.
        rewrite 2 Forall_app in Vars; rewrite Forall_app; tauto.

    (* one output *)
    - assert (self <> a)
        by (intro; subst; eapply (m_notreserved self); auto;
            do 2 setoid_rewrite InMembers_app; rewrite Hout;
            right; right; constructor; auto).

      (* get the allocated environment and memory *)
      edestruct alloc_result as (e_f & m_f &?&?&?); eauto.

      (* get the temporaries (+ the local return temporary) *)
      edestruct
        (bind_parameter_temps_exists_noout (map translate_param f.(m_in))
                                           self (type_of_inst_p (pou_name c))
                                           ((a, cltype ta) :: make_out_temps (instance_methods_temp (rev prog) f)
                                                           ++ map translate_param (m_vars f))
                                           vs (Vptr sb sofs)) as (le_f & Bind & Vars);
        eauto; try eapply NotInMembers_cons; eauto.
      assert (le_f ! self = Some (Vptr sb sofs))
        by (eapply bind_parameter_temps_implies in Bind; eauto).
      setoid_rewrite <-P_f in Bind.

      exists e_f, le_f, m_f; split.
      + constructor; auto; congruence.
      + apply match_states_conj; intuition; eauto using m_nodupvars.
        erewrite find_class_name; eauto.
        rewrite sep_swap, outputrep_singleton, sep_swap, sep_swap23,
        sep_swap34, sep_swap23, sep_swap; eauto.
        repeat rewrite map_app, map_cons, map_app in *.
        repeat rewrite translate_param_fst in Vars.
        rewrite Forall_app, Forall_cons2, Forall_app in Vars.
        setoid_rewrite sep_pure; split; [split|]; auto; try tauto.
        rewrite map_app, Forall_app; tauto.

    (* multiple outputs *)
    - assert (1 < Datatypes.length (m_out f))%nat
        by (rewrite Hout; simpl; omega).

      (* get the allocated environment and memory *)
      edestruct alloc_result as (e_f & m_f &?&?&?); eauto.

      (* get the temporaries *)
      edestruct
        (bind_parameter_temps_exists (map translate_param f.(m_in)) self (type_of_inst_p (pou_name c))
                                     out (type_of_inst_p (prefix_fun (pou_name c) (m_name f)))
                                     (make_out_temps (instance_methods_temp (rev prog) f)
                                                     ++ map translate_param f.(m_vars))
                                     vs (Vptr sb sofs) (var_ptr instb)) as (le_f & Bind & Vars); eauto.
      assert (le_f ! self = Some (Vptr sb sofs) /\ le_f ! out = Some (var_ptr instb)) as (?&?)
          by (eapply bind_parameter_temps_implies_two in Bind; eauto).
      setoid_rewrite <-P_f in Bind; setoid_rewrite <-T_f in Bind.

      exists e_f, le_f, m_f; split.
      + constructor; auto; congruence.
      + apply match_states_conj; intuition; eauto using m_nodupvars.
        erewrite find_class_name; eauto.
        rewrite sep_swap, outputrep_notnil; auto.
        erewrite find_class_name, find_method_name; eauto.
        exists instb, instco; intuition; auto.
        rewrite sep_swap23, sep_swap, sep_swap34, sep_swap23, sep_swap34,
        sep_swap45, sep_swap34, sep_swap23, sep_swap.
        setoid_rewrite sep_pure; split.
        * repeat rewrite map_app in *.
          repeat rewrite translate_param_fst in Vars.
          rewrite 2 Forall_app in Vars.
          rewrite Forall_app; tauto.
        * eapply sep_imp; eauto.
          repeat apply sep_imp'; auto.
          rewrite fieldsrep_nodup; eauto.
          erewrite <-output_match; eauto.
          rewrite translate_param_fst.
          eapply NoDup_app_weaken.
          rewrite Permutation.Permutation_app_comm, NoDup_swap, <-2 map_app.
          apply fst_NoDupMembers, m_nodupvars.
  Qed.

End FunctionEntry.

Section MainProgram.

  Variable (main_node  : ident)
           (prog       : program)
           (tprog      : Clight.program)
           (do_sync    : bool)
           (all_public : bool).
  Let tge              := Clight.globalenv tprog.
  Let gcenv            := Clight.genv_cenv tge.

  Hypothesis (TRANSL : translate do_sync all_public main_node prog = Errors.OK tprog)
             (WT     : wt_program prog).

  Let out_step   := prefix out step.
  Let t_out_step := type_of_inst (prefix_fun main_node step).

  Let main_step := main_step _ _ _ _ _ TRANSL.
  Let main_f    := main_f _ _ _ _ _ TRANSL.

  Lemma main_with_output_structure:
    forall m P,
      (1 < length (m_out main_step))%nat ->
      m |= P ->
      exists m' step_b step_co,
        alloc_variables tge empty_env m (fn_vars main_f)
                        (PTree.set out_step (step_b, t_out_step) empty_env) m'
        /\ gcenv ! (prefix_fun main_node step) = Some step_co
        /\ m' |= fieldsrep gcenv vempty step_co.(co_members) step_b ** P.
  Proof.
    intros * Len Hm.
    subst main_step main_f.
    simpl; unfold case_out.
    destruct_list (m_out (GenerationProperties.main_step _ _ _ _ _ TRANSL)) as (?,?) (?,?) ? : Out;
      try (simpl in Len; omega).

    (* get the allocated memory *)
    destruct (Mem.alloc m 0 (sizeof tge (type_of_inst (prefix_fun main_node step))))
      as (m', step_b) eqn: AllocStep.

    (* get the out struct *)
    pose proof (find_main_class _ _ _ _ _ TRANSL) as Find_main.
    pose proof (find_main_step _ _ _ _ _ TRANSL) as Find_step.
    rewrite <-Out in Len.
    edestruct global_out_struct as (step_co & Hsco & ? & Hms & ? & ? & ?); eauto.

    exists m', step_b, step_co; intuition.
    - repeat (econstructor; eauto).
    - assert (sizeof tge (type_of_inst (prefix_fun main_node step)) <= Ptrofs.modulus)
        by (simpl; setoid_rewrite Hsco; transitivity Ptrofs.max_unsigned;
            auto; unfold Ptrofs.max_unsigned; omega).
      eapply alloc_rule in AllocStep; eauto; try reflexivity.
      eapply sep_imp; eauto.
      simpl; setoid_rewrite Hsco; eapply fieldsrep_empty; eauto.
      + eapply Consistent; eauto.
      + rewrite Hms; eauto.
        intros * Hin; apply in_map_iff in Hin as ((?&?)& E' &?); inversion E'; eauto.
  Qed.

  Lemma init_mem:
    exists m sb,
      Genv.init_mem tprog = Some m
      /\ Genv.find_symbol tge (glob_id self) = Some sb
      /\ m |= staterep gcenv prog main_node mempty sb Z0.
  Proof.
    destruct Genv.init_mem_exists with (pro:=tprog) as (m' & Initmem);
      eauto using well_initialized.

    pose proof TRANSL as Trans.
    inv_trans Trans as En Estep Ereset with structs funs E.

    exists m'.
    edestruct find_self as (sb & find_step); eauto.
    exists sb; split; [|split]; auto.
    assert (NoDupMembers tprog.(AST.prog_defs)) as Nodup
        by (rewrite fst_NoDupMembers, NoDup_norepet; eapply prog_defs_norepet; eauto).
    pose proof (init_grange _ _ Nodup Initmem) as Hgrange.
    unfold make_program' in Trans.
    destruct (build_composite_env' (concat structs)) as [(ce, ?)|]; try discriminate.
    destruct (check_size_env ce (concat structs)) eqn: Check_size; try discriminate.
    unfold translate_class in E.
    apply split_map in E; destruct E as [? Funs].
    inversion Trans as [Htprog].
    rewrite <-Htprog in Hgrange at 2.
    simpl in Hgrange.
    setoid_rewrite find_step in Hgrange.
    rewrite <-Zplus_0_r_reverse in Hgrange.
    rewrite Zmax_left in Hgrange;
      [|destruct (ce ! main_node); try omega; apply co_sizeof_pos].
    apply sep_proj1 in Hgrange.
    rewrite sepemp_right in *.
    eapply sep_imp; eauto.
    rewrite pure_sepwand.
    - unfold Genv.perm_globvar; simpl.
      transitivity (range_w sb 0 (sizeof gcenv (type_of_inst main_node))).
      + unfold sizeof; simpl.
        subst gcenv tge.
        setoid_rewrite <-Htprog; auto.
      + apply range_staterep; eauto.
        * eapply Consistent; eauto.
        * eapply make_members_co; eauto.
        * intro En'; rewrite En' in En; discriminate.
    - edestruct make_members_co as (co & Find_main & ? & ? & ? & ? & ?); eauto.
      subst gcenv tge.
      rewrite <-Htprog in Find_main; simpl in Find_main.
      rewrite Find_main.
      transitivity Ptrofs.max_unsigned; auto; unfold Ptrofs.max_unsigned; omega.
  Qed.

End MainProgram.

Hint Resolve match_states_wt_state bounded_struct_of_class_ge0. *)
