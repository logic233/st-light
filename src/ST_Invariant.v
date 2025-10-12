
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
                  match field_offset ge x (mk_members  po) with
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
      match field_offset ge x (mk_members  po) with
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

  Hint Resolve Z.divide_trans.
  Lemma staterep_deref_mem:
    forall m me po_name  po pro b ofs d x ty v P,
      find_pou_decl po_name pro = Some po ->
      m |= staterep gcenv pro po_name me b ofs ** P ->
      In (x, ty)  ( po.(pou_vars)  ) ->
      is_inst ty = false ->
      find_val x me = Some v ->
      field_offset gcenv x (mk_members po)= Errors.OK d ->
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
      exists d, field_offset gcenv x (mk_members po) = Errors.OK d
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
    destruct (field_offset gcenv x (mk_members po)).
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
    struct_in_bounds gcenv 0 Ptrofs.max_unsigned (Ptrofs.unsigned sofs) (mk_members po)  ->
    exists d, field_offset gcenv x (mk_members po) = Errors.OK d
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
  destruct (field_offset gcenv x (mk_members po))  eqn:H11 .
  + 
   exists z; split; auto.
   eapply struct_in_bounds_field in HB; eauto.
  + destruct (get_pou_name ty);    contradict Hm.
Qed. 


    Lemma staterep_extract:
    forall   me b ofs m i po_name' po  P pro pro' pou_name,
      wt_project pro  ->
      find_pou pou_name pro = Some (po,pro') ->
      (In (i,Tinst po_name')  po.(pou_vars) /\
      m |= staterep gcenv pro pou_name me b ofs ** P)
      -> exists  d,
           field_offset gcenv i (mk_members po) = Errors.OK d
          /\ m |= staterep gcenv pro po_name' (instance_match i me) b (ofs + d)
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
    destruct (field_offset gcenv i (mk_members  po)) as [d|].
  
    + exists d. intuition;eauto.
      assert (In (i, Tinst po_name') (pou_vars po))
          by (rewrite E, in_app; right; apply in_eq).
      apply find_pou_app  in Find as (prog''&?&Find);subst.
      rewrite staterep_skip_app, staterep_skip_cons; auto.
      eapply wt_program_not_same_name; eauto;eapply wt_program_app; eauto.
      eapply wt_program_not_class_in; eauto.
    + destruct Hmem; contradiction.
  Qed.
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
    struct_in_bounds ge 0 Ptrofs.max_unsigned (Ptrofs.unsigned sofs) (mk_members  po ) .

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

    Lemma match_states_assign_state_mem:
      m |= match_states pro po  (me, ve) (e, cte) sb sofs
           ** P ->
      In (x, ty) ( po.(pou_vars)) ->
      is_inst ty = false ->
      exists m' d,
        field_offset ge x (mk_members po) = Errors.OK d
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
      destruct (field_offset ge x (mk_members po)) as [d|] eqn: Hofs;try (destruct Hmem; contradiction).

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
