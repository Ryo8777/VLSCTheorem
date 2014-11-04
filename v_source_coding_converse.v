Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finfun finset bigop.
Require Import Reals Fourier.
Require Import Reals_ext log2 ssr_ext Rbigop proba entropy aep typ_seq natbin Rssr ceiling v_source_coding_direct divergence channel log_sum v_source_code extension.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope tuple_ext_scope.
Local Open Scope typ_seq_scope.
Local Open Scope proba_scope.
Local Open Scope reals_ext_scope.
Local Open Scope entropy_scope.
Local Open Scope divergence_scope.
Local Open Scope channel_scope.

(* ctr c + ctr v => Command input*)
(* ctr c + ctr v + Search " _ " or ctr c + ctr l *)
(* boolのイコールを示すには apply /_____ /____. _____はview(ifPとか)をかける *)
(* nesym = not_eq_sym
     : forall (A : Type) (x y : A), x <> y -> y <> x *)
(*SSRでよかったこと、Coqだったら大変だっただろうなってこと。*)
(*Affeldtさんのcheat sheat見ておく*)
(*inversion 模倣、双模倣*)
(*rewrite ?mulRA.*)

Section log_sum_ord.
Variable A : finType.
Variable n: nat.
Variable f g: nat -> R+.
Hypothesis f_dom_by_g : f << g.

Lemma log_sum_inequality_ord:
  \rsum_(i| i \in 'I_n) (f i * (log (f i / g i))) >= 
  (\rsum_(i| i \in 'I_n) f i) * (log ((\rsum_(i| i \in 'I_n) f i) / (\rsum_(i| i \in 'I_n) g i))).
Proof.
have Rle0f': forall (x : ordinal_finType n), 0 <= f x by move=> ?; apply:(Rle0f f).
have Rle0g': forall (x : ordinal_finType n), 0 <= g x by move=> ?; apply:(Rle0f g).
have H:forall h, \rsum_(a | a \in [set: 'I_n]) h a = \rsum_(a | a \in  'I_n) h a. 
  by move=>?; apply:eq_bigl=>?; rewrite in_setT.
rewrite -!H /=; apply: Rle_ge.
by apply: (log_sum [set: 'I_n] (mkPosFun Rle0f') (mkPosFun Rle0g') f_dom_by_g).
Qed.

Lemma log_sum_inequality_ord_add1: 
  \rsum_(i| i \in 'I_n) f i.+1 * (log (f i.+1 / g i.+1)) >= 
  (\rsum_(i| i \in 'I_n) f i.+1) * (log ((\rsum_(i| i \in 'I_n) f i.+1) / (\rsum_(i| i \in 'I_n) g i.+1))).
Proof.
have Rle0f_add1: forall (x : ordinal_finType n), 0 <= f x.+1 by move=> ?; apply:(Rle0f f).
have Rle0g_add1: forall (x : ordinal_finType n), 0 <= g x.+1 by move=> ?; apply:(Rle0f g).
have f_dom_by_g1 : (mkPosFun Rle0f_add1) << (mkPosFun Rle0g_add1).
  by rewrite /dom_by=>?; apply:f_dom_by_g.
have H:forall h, \rsum_(a | a \in [set: 'I_n]) h a.+1 = \rsum_(a | a \in  'I_n) h a.+1.
  by move=>?; apply:eq_bigl=>?; rewrite in_setT.
rewrite -!H -(H (fun i => f i * log (f i / g i))); apply: Rle_ge.
apply: (log_sum [set: 'I_n] (mkPosFun Rle0f_add1) (mkPosFun Rle0g_add1) f_dom_by_g1).
Qed.

Lemma log_sum_inequality_ord_add1':
  \rsum_(i| i \in 'I_n) f i.+1 * (log (f i.+1) - log (g i.+1)) >= 
  (\rsum_(i| i \in 'I_n) f i.+1) * (log (\rsum_(i| i \in 'I_n) f i.+1) - log (\rsum_(i| i \in 'I_n) g i.+1)).
Proof.
rewrite [X in X >= _](_ : _ = \rsum_(i | i \in 'I_n) f i.+1 * log (f i.+1 / (g i.+1))).
  rewrite [X in _ >= X](_ : _ =  (\rsum_(i | i \in 'I_n) f i.+1) *
   (log ((\rsum_(i | i \in 'I_n)f i.+1) / (\rsum_(i | i \in 'I_n) g i.+1)))).
      by apply: log_sum_inequality_ord_add1.
  have :0 <= \rsum_(i | i \in 'I_n) f i.+1 by apply: Rle_big_0_P_g=>i _; apply: Rle0f.
  case=>[Hf | <-]; last by rewrite !mul0R.
  have : 0 <= \rsum_(i | i \in 'I_n) g i.+1 by apply: Rle_big_0_P_g=>i _; apply: Rle0f.
  case=>[Hg |].
    rewrite log_mult//; last by apply: Rinv_0_lt_compat.
    by rewrite log_Rinv.
  have Rle0g_add1: forall (x : ordinal_finType n), 0 <= g x.+1 by move=> ?; apply:(Rle0f g).
  move/(Req_0_rmul_inv (fun i => i \in 'I_n) _ Rle0g_add1)=>eq_g_0.
  have : 0 = \rsum_(i | i \in 'I_n) f i.+1.
    by apply:Req_0_rmul=>i _; apply:esym; apply: (@f_dom_by_g i.+1); rewrite -eq_g_0.
  by move=>tmp; move:Hf; rewrite -tmp; move/Rlt_not_eq.
apply: eq_bigr=>i _.
case:(Rle0f f i.+1)=>[fpos|<-]; last by rewrite !mul0R.
  case:(Rle0f g i.+1)=>[gpos|]; last by  move/esym/(@f_dom_by_g i.+1)->; rewrite !mul0R.
  rewrite log_mult//; last by apply: Rinv_0_lt_compat.
  by rewrite log_Rinv.
Qed.

End log_sum_ord.

Section Ordinal.

Variable T : finType.
Variable f : T -> nat.

Definition inordf t := inord (f t) : [finType of 'I_(\max_t f t).+1].

Lemma inordf_eq : f =1 inordf.
Proof. move=> t; rewrite /inordf inordK //; by apply: leq_bigmax. Qed.

End Ordinal.

Prenex Implicits inordf.

Section big_pow.

Variable x : R.
Hypothesis neq_x_1 : x <> 1.

Lemma big_pow1 n: \rsum_(i | i \in 'I_n) x ^ i.+1 = x * (1 - (x ^ n)) / (1 - x).
Proof.
apply: (Rplus_eq_reg_l 1).
rewrite /Rdiv {1}[in RHS](Rinv_r_sym (1 - x)); last by apply:Rminus_eq_contra; apply: nesym.
rewrite Rmult_plus_distr_l mulR1 -Rmult_plus_distr_r addRA /Rminus [in RHS]addRC -addRA.
rewrite Rplus_opp_l addR0 (addRC _ 1) Ropp_mult_distr_r_reverse.
rewrite -(big_mkord xpredT (fun i => x ^ i.+1)) (_ : n = n.+1.-1) //.
rewrite -(big_add1 _ _ _ _  xpredT)-{1}(pow_O x) -big_ltn//.
by rewrite big_mkord -sum_f_R0_rsum tech3.
Qed.

Lemma log_pow n r: 0 < r -> log (r ^ n) = (INR n) * log r.
Proof.
elim:n=> [|n' IH lt_0_r]; first by rewrite log_1 mul0R.
rewrite log_mult//;last by apply:pow_lt.
by rewrite IH // -addn1 addRC plus_INR Rmult_plus_distr_r mul1R.
Qed.

End big_pow.

Section Lem_entropy.

Variable A : finType.
Variable P : dist A.
Variable n : nat.

Lemma entropy_TupleDist : `H (P `^ n) = (INR n) * `H P.
Proof.
elim:n=>[|n0 IH]. 
  rewrite /entropy /= /TupleDist.f rsum_0tuple /=.
  by rewrite big_ord0 log_1 mulR0 mul0R Ropp_0.
rewrite S_INR Rmult_plus_distr_r mul1R -IH.
rewrite /entropy -big_head_behead /= /TupleDist.f /=. 
rewrite -Ropp_plus_distr; apply:Ropp_eq_compat.
rewrite [X in X = _](_ :_ = \rsum_(i | i \in A) P i * log (P i) * 
          (\rsum_(j | j \in [finType of n0.-tuple A]) (\rmul_(i0<n0) P j \_ i0)) +
           \rsum_(i | i \in A) P i * \rsum_(j | j \in [finType of n0.-tuple A])
          (\rmul_(i0<n0) P j \_ i0) * log (\rmul_(i0<n0) P j \_ i0)); last first.
  rewrite -big_split /=.
  apply:eq_bigr=> i _.
  rewrite -mulRA -Rmult_plus_distr_l (mulRC (log (P i))) (big_distrl (log (P i)) _ _) /=.
  rewrite -big_split /= big_distrr/=.
  apply: eq_bigr=>i0 _.
  rewrite big_ord_recl tnth0 -mulRA.
  case:(Rle0f P i)=>[ pi_pos| <-]; last by rewrite !mul0R.
  apply:Rmult_eq_compat_l.
  rewrite -Rmult_plus_distr_l.
  rewrite  (@eq_bigr _ _ _ _ _ _ (fun x => P [tuple of i :: i0] \_ (lift ord0 x)) (fun x => P i0 \_ x))=>[|i1 _]; last first.
    by rewrite (tnth_nth (tnth_default i0 i1)) /tnth lift0 /=.
  case: (Req_dec 0 (\rmul_(i'<n0) P i0 \_ i'))=>[<-|rmul_non0].
    by rewrite !mul0R.
  have rmul_pos: 0 < \rmul_(i1<n0) P i0 \_ i1.
    apply:Rlt_le_neq=>//.
    by apply:Rle_0_big_mult=>?; apply:Rle0f.
  by rewrite log_mult // !Rmult_plus_distr_l mulRA mulRA.
rewrite TupleDist.f1 -big_distrl /= mulR1.
rewrite [in RHS]addRC.
apply:Rplus_eq_compat_l.
by rewrite -big_distrl/= pmf1 mul1R.
Qed.

End Lem_entropy.


Section le_H_N.

Variable (A : finType) (P : dist A) (enc : A -> seq bool).
Definition ell x := size (enc x).
Definition X := mkRvar P (fun x => INR (ell x)).
Definition Nmax := (\max_(a| a \in A) ell a).
Definition I_lmax := [finType of 'I_Nmax.+1 ].
Hypothesis enc_uniq : uniquely_decodable _ _ enc.

Lemma Xnon0 x : 0 <> X x.
Proof.
rewrite /X/= /ell.
case:(Req_dec 0 (INR (ell x)))=>// H.
move:H; rewrite (_ : 0 = INR 0)//; move/INR_eq.
move/esym/size0nil=>encx_nil.
move:(@enc_uniq [::] ([:: x])).
rewrite /extension /= encx_nil cat0s=>H.
have nil: [::] = [::] by[].
by move:(H (nil bool)).
Qed.

Lemma Xpos a: 0 < X a.
Proof.
move/nesym/INR_not_0:(@Xnon0 a)=>H.
apply: lt_0_INR; apply/ltP.
move:(leq0n (ell a)); rewrite /X/= leq_eqVlt.
by move=>tmp; move:tmp H; case/orP=>// /eqP ->.
Qed.

Lemma Rle0Pr (i : 'I_Nmax.+1) : 0 <= Pr[X = (INR i)]. Proof. by apply:le_0_Pr. Qed.

Definition PN := mkPosFun Rle0Pr.

Lemma pmf1_PN : \rsum_(i | i \in I_lmax) PN i = 1.
Proof.
rewrite -(pmf1 P).
rewrite [in RHS](partition_big (inordf ell) (fun i => i \in 'I_Nmax.+1)) //=.
apply:eq_bigr=> i _; apply:eq_bigl=>i0.
rewrite /= inE.
apply/eqP/eqP; first by move/INR_eq; rewrite inordf_eq; apply:ord_inj.
by rewrite inordf_eq; move->.
Qed.

Lemma PN_1 : \rsum_(a |a \in I_lmax) PN a = 1. Proof. by apply: pmf1_PN. Qed.

Definition Ndist := mkDist PN_1.
Definition N := mkRvar Ndist (fun x => INR x).

Lemma Ex_ord : `E X = \rsum_(i | i \in I_lmax) (INR i) * PN i.
Proof.
rewrite /Ex_alt (partition_big (inordf ell) (fun i => i \in 'I_Nmax.+1)) //=.
apply:eq_bigr=> i _.
rewrite /@pr /Pr mulRC big_distrl /=.
rewrite [in RHS]rsum_mulRC.
apply: congr_big=> [//| x | i0]; last by rewrite inordf_eq; move/eqP->.
rewrite inE; apply/eqP/eqP; first by rewrite inordf_eq; move->. 
by move/INR_eq; rewrite inordf_eq; move/val_inj.
Qed.

Lemma cond_eq_Ex_1 a : `E X = 1 -> X a <> 1 -> 0 = P a.
Proof.
rewrite /Ex_alt /= -{1}(pmf1 P)=>Ex1 Xnon1.
have : forall i : A, i \in A -> P i <= INR (ell i) * P i.
  move=> i _; rewrite -{1}(mul1R ( P i)). 
  apply:Rmult_le_compat_r; first apply:Rle0f.
  rewrite (_ : 1 = INR 1) //.
  move: (Xpos i); rewrite /= (_ : 0 = INR 0) //.
  by move/INR_lt/lt_le_S/le_INR.
move/Rle_big_eq=>H.
case: (Req_dec (P a) 0)=>//.
have: INR (ell a) * P a = P a by rewrite (H Ex1 a).
rewrite -{2}(mul1R (P a)).
by move/Rmult_eq_reg_r=>tmp /tmp.
Qed.

Lemma HN_0 : `E X = 1 -> `H Ndist = 0.
Proof.
move/cond_eq_Ex_1=>cond_eq_Ex_1.
rewrite /entropy Ropp_eq_0_compat //.
rewrite {2}(Req_0_rmul (fun i => i \in I_lmax) (fun i => 0))//.
apply:eq_bigr=> i _; rewrite /= /@pr /Pr.
case (Req_dec (INR i) 1)=>[->| neq0].
  have ->: \rsum_(a | a \in [set x | INR (ell x) == 1]) P a = 1; last by rewrite log_1 mulR0.
  rewrite -{2}(pmf1 P).
  rewrite [in RHS](bigID (fun a => a \in [set x | INR (ell x) == 1])) /=.
  have <-: 0 = \rsum_(i0 | i0 \notin [set x | INR (ell x) == 1]) P i0; last by rewrite addR0.
  apply:Req_0_rmul=>i0.
  rewrite inE; move/eqP.
  by apply: (cond_eq_Ex_1 i0).
have <-: 0 = \rsum_(a | a \in [set x | INR (ell x) == INR i]) P a; last by rewrite mul0R.
apply:Req_0_rmul=>i0.
rewrite inE; move/eqP=>eq_tonat_i.
move:neq0; rewrite -eq_tonat_i.
by apply: (cond_eq_Ex_1 i0).
Qed.

Lemma le_1_Ex : 1 <= `E X .
Proof.
rewrite -(pmf1 P).
apply:Rle_big_P_f_g=>i _.
rewrite -{1}(mul1R ( P i)). 
apply:Rmult_le_compat_r; first by apply:Rle0f.
rewrite (_ : 1 = INR 1) //; move: (Xpos i).
by rewrite /= (_ : 0 = INR 0)//; move/INR_lt/lt_le_S/le_INR.
Qed.

Lemma Ex_pos: 0 < `E X.
Proof. by apply:(Rlt_le_trans _ _ _ Rlt_0_1 le_1_Ex). Qed. 

Lemma Ex_non0: `E X <> 0.
Proof. by apply:nesym; apply:Rlt_not_eq; apply: Ex_pos. Qed.

Lemma big_ord_exclude0 n (h:nat -> R): h 0%nat = 0 -> 
    \rsum_(i | i \in 'I_n.+1) h i = \rsum_(i | i \in 'I_n) h i.+1.
Proof.
move=>H.
rewrite -(big_mkord xpredT _) -(big_mkord xpredT (fun i => h i.+1)).
by rewrite big_ltn// H add0R big_add1.
Qed.

Lemma le_HN_logE_loge' : 
  `H Ndist <= `E X * log (`E X) - (`E X - 1) * log((`E X) -1).
Proof.
move: Ex_pos Ex_non0=>Ex_pos Ex_non0.
move/Rle_lt_or_eq_dec:le_1_Ex=>[lt_Ex_1| eq_E_0]; last first.
  rewrite -eq_E_0 /Rminus Rplus_opp_r mul0R Ropp_0 addR0 mul1R log_1.
  by move/esym/HN_0:eq_E_0->; apply:Rle_refl.
have lt_0_EX_1 : 0 < `E X - 1.
  apply:(Rplus_lt_reg_r 1).
  by rewrite addR0 addRC -addRA Rplus_opp_l addR0.
pose alp := (`E X - 1) / `E X.
have gt_alp_1 : alp < 1.
    apply:(Rmult_lt_reg_r (`E X)); first by apply:(Rlt_trans _ _ _ (Rlt_0_1)).
    rewrite /alp mul1R -mulRA -Rinv_l_sym // mulR1.
    by apply:Rgt_lt; apply:(tech_Rgt_minus _ _ (Rlt_0_1)).
have lt_0_alp : 0 < alp.
  rewrite /alp.
  by apply:Rlt_mult_inv_pos=>//.
have Ex_pos' : 0 < 1 - (`E X - 1) * / `E X.
  rewrite Rmult_plus_distr_r -Rinv_r_sym // Ropp_mult_distr_l_reverse mul1R /Rminus.
  rewrite Ropp_plus_distr addRA Ropp_involutive addRC Rplus_opp_r addR0.
  by apply: Rinv_0_lt_compat.
have max_pos: (0 < \max_(a in A) ell a)%coq_nat.
  apply:ltP.
  move/card_gt0P:(dist_support_not_empty P)=>[a _].
  apply:(bigmax_sup a)=> //.
  by move:(Xpos a); rewrite /X /= (_ : 0 = INR 0)//;move/INR_lt/ltP.

rewrite [X in _ <= X](_ :_ = log ( alp / (1 - alp)) - (log alp) * `E X); last first.
  rewrite /alp /Rdiv !log_mult  //; last first.
      by apply: Rinv_0_lt_compat. 
    by apply: Rinv_0_lt_compat.
  rewrite !log_Rinv //.
  rewrite Rmult_plus_distr_r /Rminus [in RHS]addRC (addRC _ (- log (`E X) * `E X)).
  rewrite Ropp_plus_distr !Ropp_mult_distr_l_reverse Ropp_involutive mulRC -addRA. 
  apply: Rplus_eq_compat_l.
  rewrite Rmult_plus_distr_r mulRC Ropp_plus_distr -Ropp_mult_distr_l_reverse.
  apply: Rplus_eq_compat_l.
  rewrite Ropp_mult_distr_l_reverse Ropp_involutive mul1R -addRA -{1}(addR0 (log (`E X + -1))).
  apply: Rplus_eq_compat_l.
  rewrite Rmult_plus_distr_r -Rinv_r_sym // Ropp_mult_distr_l_reverse mul1R.
  rewrite  Ropp_plus_distr Ropp_involutive (addRC 1 _) (addRC (-1) _).
  by rewrite -addRA Rplus_opp_l addR0 log_Rinv //Ropp_involutive Rplus_opp_l.

apply:(Rle_trans _  (log (alp * (1 - (alp ^ (\max_(a| a \in A) ell a))) / (1 - alp))
                     - log alp * `E X) _); last first.
  apply:Rplus_le_compat_r.
  apply:log_increasing_le.
    apply:Rmult_lt_0_compat; last by  apply: Rinv_0_lt_compat ; apply:Rgt_lt; apply:Rgt_minus.
    apply:Rmult_lt_0_compat=> //. 
    apply:Rgt_lt; apply:Rgt_minus; apply:Rlt_gt.
    have : 0 <= alp < 1 by apply:conj=> //; first apply:Rlt_le.
     by move/(pow_lt_1_compat _ _ ):max_pos=>tmp; move/tmp/proj2.
  rewrite /Rdiv -mulRA.
  apply:Rmult_le_compat_l; first by apply:Rlt_le.
  rewrite -{2}(mul1R (/ (1 - alp))) ; apply:Rmult_le_compat_r.
    by apply:Rlt_le; apply:Rinv_0_lt_compat; apply:Rgt_lt; apply:Rgt_minus; apply:Rlt_gt.
  rewrite -{2}(addR0 1) /Rminus; apply:Rplus_le_compat; first by apply:Rle_refl.
  apply:Rge_le; apply:Ropp_0_le_ge_contravar.
  by apply:pow_le; apply:Rlt_le.

rewrite Ex_ord -big_pow1; last by apply:Rlt_not_eq.
rewrite mulRC (big_morph _ (morph_mulRDl _) (mul0R _)).
apply:(Rplus_le_reg_r (\rsum_(i|i \in I_lmax) INR i * Pr[X = (INR i)] * log alp)).
rewrite -addRA Rplus_opp_l addR0.
rewrite  (@eq_bigr _ _ _ I_lmax _ _ _ (fun i => Pr[X = (INR i)] * log (alp ^ i))); last first.
  by move=> i _; rewrite log_pow // [in RHS]mulRC -mulRA (mulRC _ (log alp)) mulRA.
rewrite /entropy addRC; move:Ropp_minus_distr; rewrite/Rminus; move<-.
rewrite -(Ropp_involutive (log _)).
apply:Ropp_le_contravar; apply:Rge_le.
rewrite (big_morph _ morph_Ropp Ropp_0).
rewrite -big_split /=.
rewrite [X in X >= _](_ : _ =  \rsum_(i|i\in I_lmax)
      Pr[X = (INR i)] * (log Pr[X = (INR i)] - log (alp ^ i))); last first.
  by apply:eq_bigr=>i _; rewrite Rmult_plus_distr_l Ropp_mult_distr_r_reverse.
rewrite -Rminus_0_l -(mul1R (0 - _)).

have pmf1': \rsum_(i | i\in 'I_(\max_(a in A) ell a)) Pr[X = (INR i.+1)] = 1.
  rewrite -pmf1_PN /PN /=.
  rewrite (@big_ord_exclude0 _ (fun x => Pr[X = (INR x)])); first by[].
  apply:esym; apply:Req_0_rmul=> i.
  rewrite inE; move/eqP=> Xi_0.
  by move/Rlt_not_eq:(Xpos i); rewrite Xi_0.
rewrite -{2}log_1 -pmf1'.
have Rle0Pr (i : nat): 0 <= Pr[X = (INR i)] by apply:Rle_big_0_P_g=>? _;  apply:(Rle0f P).
have Rle0alpi (i : nat): 0 <= alp ^ i by apply:pow_le; apply:Rlt_le.
pose f := mkPosFun Rle0Pr.
pose g := mkPosFun Rle0alpi.
have dom_by_fg:  f << g.
  move=> i; move/pow0_inv=>alp0.
  by move:lt_0_alp; rewrite alp0;move/Rlt_not_eq.
rewrite /I_lmax/=/Nmax.
rewrite (@big_ord_exclude0 _ (fun i => Pr[X = (INR i)] * (log Pr[X = (INR i)] - log (alp ^ i)))); last first.
  rewrite /@pr/Pr.
  have ->: [set x | X x == INR 0] = set0; last by rewrite big_set0 mul0R.
  apply/setP=>i; rewrite inE/=in_set0.
  by apply/eqP; apply: nesym; apply: Rlt_not_eq; apply: Xpos.
by move: (log_sum_inequality_ord_add1' (\max_(a in A) ell a) dom_by_fg).
Qed.

Lemma le_HN_logE_loge : `H Ndist <= log (`E X) + log (exp 1).
Proof.
move: Ex_pos Ex_non0=>Ex_pos Ex_non0.
move/Rle_lt_or_eq_dec:le_1_Ex=>[? | eq_Ex_1]; last first.
  rewrite -eq_Ex_1 log_1 add0R.
  by move/esym/HN_0:eq_Ex_1->; apply:log_exp1_Rle_0.
have Ex_1 : 0 < `E X - 1.
  apply:(Rplus_lt_reg_r 1).
  by rewrite addR0 addRC -addRA Rplus_opp_l addR0.
have neq_Ex1_0 :(`E X + -1) <> 0.
  by apply:nesym; apply:Rlt_not_eq.
apply:(Rle_trans _ (`E X * log (`E X) - (`E X - 1) * log((`E X) -1)) _).
  by apply:le_HN_logE_loge'.
rewrite {1}(_ :`E X = (1 + (`E X - 1))); last by rewrite /Rminus addRC -addRA Rplus_opp_l addR0.
rewrite Rmult_plus_distr_r mul1R /Rminus -addRA; apply:Rplus_le_compat_l.
rewrite -Ropp_mult_distr_r_reverse -Rmult_plus_distr_l -(mul1R (log (exp 1))).
rewrite -{3}(Rplus_minus (`E X) 1) -Ropp_minus_distr'. 
apply:div_diff_ub=>//; first by apply:Rlt_le.
by apply:Rlt_le; apply:(Rlt_trans _ _ _ (Rlt_0_1)).
Qed.

End le_H_N.


Section Bigop_Lemma.
Variable A : finType.
Variable P : dist A.
Variable n : nat.
Variable f : A -> seq bool.
Hypothesis f_inj : injective f.

Lemma big_seq_tuple (F : seq bool -> R): (0 < #|A|)%nat ->
  \big[Rplus/0]_(i <- [seq f i | i <- index_enum A] | size i == n) F i =
  \big[Rplus/0]_(i : n.-tuple bool | tval i \in codom f) F i.
Proof.
move Hpick : [pick x | x \in [set: A] ] => p Anon0.
move: Hpick; case: (pickP _)=>[defaultA _ _ | abs]; last first.  
  suff : False by [].
  move:Anon0.
  rewrite -cardsT card_gt0; case/set0Pn => ?.
  by rewrite abs.
rewrite big_map.
 pose dummy := [tuple of nseq n false].
 pose h (i : n.-tuple bool) := odflt defaultA [pick a | f a == i].
 pose h' a : n.-tuple bool := insubd dummy (f a).
 have H a : odflt defaultA [pick a0 | f a0 == f a ] = a.
 - case: pickP => /=; last by move/(_ a); rewrite eqxx.
   by move => a0 /eqP /f_inj ->.
 - rewrite (reindex_onto h h'); last first.
   + move => a sizefa. rewrite /h' /h insubdK //.
   + apply: esym.
     apply: eq_big => i; last by move/codomP => [a fa]; rewrite /h fa H.
     apply/idP/andP.
     * move/codomP => [a fa]. rewrite /h fa H.
       split; first by rewrite -fa size_tuple eqxx.
       by rewrite /h' -fa valKd.
     * rewrite /h /h' => [] [sizefhi /eqP <-]; rewrite insubdK //.
       exact: codom_f.
Qed.

End Bigop_Lemma.

Section converse_pre.

Variable A : finType.
Variable P : dist A.
Variable n : nat.

Variable f : A -> seq bool.
Local Notation "'I_lmax'" := (I_lmax f).
Local Notation "'X'" := (X P f).
Local Notation "'Ndist'" := (Ndist P f).
Hypothesis f_uniq: uniquely_decodable _ _ f.
Local Notation "'Nmax'" := (Nmax f).

Definition Pf (i : seq bool) := 
    if [ pick x | f x == i ] is Some x then P x else 0.

Lemma pmf1_Pf: \rsum_(m| m \in I_lmax) \rsum_(a | a \in [finType of m.-tuple bool]) Pf a = 1.
Proof.
move:(uniq_dec_inj _ _ _ f_uniq)=> f_inj.
rewrite -(pmf1 P) (partition_big (inordf (ell f)) (fun i => i \in 'I_Nmax.+1)) //=.
apply:eq_bigr=>i _.
rewrite (eq_bigr (fun a => if (tval a \in codom f) then Pf a else 0)).
  rewrite -big_mkcondr/= -big_seq_tuple //; last by apply: dist_support_not_empty.
  rewrite (big_map f (fun i0 => size i0 == i) (fun x => Pf x )) /=.
  apply:eq_big=>[?| i0]; first by rewrite (inordf_eq (fun x => size (f x))). 
  rewrite /Pf.
  by case:(pickP ) =>[x /eqP /f_inj ->| /(_ i0)]; last rewrite eqxx.
move=>x _.
rewrite /Pf.
case:(pickP ) =>[? /eqP <-| _ ]; first by rewrite codom_f.
by case:ifP.
Qed.

Check [set x : I_lmax | Pr[X = INR x] != 0].

Lemma disjoint_0 : [disjoint [set x : I_lmax | Ndist x == 0] & [set x : I_lmax | Ndist x != 0]].
Proof.
rewrite disjoints_subset.
rewrite /setC.
rewrite (_ : [set x | x \notin [set x0: I_lmax | Pr[X = (INR x0)] != 0]] = [set x:I_lmax | Pr[X = (INR x)] == 0]); first by[].
apply/setP=>i.
rewrite !inE.
by case:(Pr[X = (INR i)] == 0); rewrite -negb_involutive_reverse.
Qed.

Lemma setU_0 : [set: I_lmax] = [set x : I_lmax | Ndist x != 0] :|: [set x : I_lmax | Ndist x == 0].
Proof.
rewrite setUC.
by apply/setP=> ?; rewrite !inE orbN.
Qed.

Lemma entropy_l2 : `H P =  - \rsum_(m| m \in [set x : I_lmax | Ndist x != 0]) \rsum_(a | a \in [finType of m.-tuple bool]) Pf a * log (Pf a).
Proof.
rewrite entropy_l1.
apply:Ropp_eq_compat.
rewrite [X in X = _](_:_ = \rsum_(m | m \in [set : I_lmax])
      \rsum_(a | a \in [finType of m.-tuple bool]) Pf a * log (Pf a)); last first.
  by apply:eq_bigl=>i; rewrite in_setT.
rewrite (rsum_union _ _ _ _ disjoint_0 setU_0).
have-> : \rsum_(m | m \in [set x : I_lmax | Pr[X = (INR x)] == 0])
      \rsum_(a | a \in [finType of m.-tuple bool]) Pf a * log (Pf a) = 0.
  apply:esym; apply: Req_0_rmul=>i.
  rewrite inE /@pr /Pr/=.
  move/eqP/Rle_big_eq_0=>H.
  have {H}H: forall i0 : A, i0 \in [set x | INR (ell f x) == INR i] -> P i0 = 0.
    apply:H=> ? ?; by apply:Rle0f.
  apply:Req_0_rmul=>i0 i_in.
  rewrite /Pf.
  case:pickP=>[x /eqP fx_i0|?]; last by rewrite mul0R.
  have ->: P x = 0.
    apply:H.
    rewrite inE /ell fx_i0.
    by rewrite size_tuple.
  by rewrite mul0R.
by rewrite addR0.
Qed.

Lemma entropy_l3 : `H P = -  \rsum_(m| m \in [set x : I_lmax | Ndist x != 0]) 
Ndist m * (\rsum_(a | a \in [finType of m.-tuple bool]) Pf a / (Ndist m) * 
(log ((Pf a) / (Ndist m)) + log (Ndist m))).
Proof.
rewrite entropy_l2.
apply:Ropp_eq_compat.
apply:eq_bigr=>i. 
rewrite inE ;move/eqP=>Pr_non0.
rewrite big_distrr /=.
apply:eq_bigr=>i0 _. 
rewrite [in RHS]mulRC /Rdiv -mulRA -mulRA.
case: (Req_dec (Pf i0) 0)=>[->| /nesym ?]; first by rewrite !mul0R.
apply:Rmult_eq_compat_l.
rewrite mulRC -mulRA.
rewrite -Rinv_r_sym // mulR1 log_mult.
    rewrite log_Rinv; first by rewrite -addRA Rplus_opp_l addR0.
    apply:Rlt_le_neq; first by apply:le_0_Pr.
    by apply:nesym.
  apply:Rlt_le_neq=>//.
  rewrite /Pf; case:pickP=>[? _ | ? ]; first by apply:Rle0f.
  by apply:Rle_refl.
apply:Rinv_0_lt_compat.
apply:Rlt_le_neq; first by apply:le_0_Pr.
by apply:nesym.
Qed.

Lemma entropy_Ndist : `H Ndist = - \rsum_(m| m \in [set x : I_lmax | Ndist x != 0]) 
Ndist m * log (Ndist m).
Proof.
rewrite /entropy; apply:Ropp_eq_compat.
rewrite [X in X = _](_:_ = \rsum_(m | m \in [set : I_lmax]) Ndist m * log (Ndist m)); last first.
  by apply:eq_bigl=>i; rewrite in_setT.
rewrite (rsum_union _ _ _ _ disjoint_0 setU_0).
rewrite [X in _ + X = _](_ :_ = 0); first by rewrite addR0.
apply:esym; apply: Req_0_rmul=>i.
rewrite inE /Ndist /=.
by move/eqP->; rewrite mul0R.
Qed.

Lemma entropy_l4 : `H P =  \rsum_(m| m \in [set x : I_lmax | Ndist x != 0]) 
Ndist m * (- \rsum_(a | a \in [finType of m.-tuple bool]) Pf a / (Ndist m) * 
(log ((Pf a) / (Ndist m)))) + `H Ndist.
Proof.
rewrite entropy_l3 entropy_Ndist.
rewrite !(big_morph _ morph_Ropp Ropp_0).
rewrite -big_split/=.
apply:eq_bigr=>i.
rewrite inE ;move/eqP=>H.
rewrite Ropp_mult_distr_r_reverse -Ropp_plus_distr; apply:Ropp_eq_compat.
rewrite -Rmult_plus_distr_l; apply:Rmult_eq_compat_l.
have distPf: \rsum_(a | a \in [finType of i.-tuple bool]) Pf a / Pr[(Top.X P f) = (INR i)] = 1.
  rewrite /Rdiv -big_distrl /=.
  apply:(Rmult_eq_reg_r (Pr[(Top.X P f) = (INR i)]))=>//.
  rewrite -mulRA -Rinv_l_sym // mul1R mulR1 /@pr /Pr /=.  
  rewrite /ell.
  rewrite [X in _ = X](_ : _ =  \rsum_(i0 | i0 \in [set x | INR (size (f x)) == INR i]) Pf (f i0)); last first.
    apply:eq_bigr=>a ain.
    rewrite /Pf.
    have -> : [pick x | f x == f a ] = Some a; last by[].
      case:pickP; first by move=>x /eqP/ f_inj ->.
      by move/(_ a); rewrite eqxx.                                   
rewrite [X in _ = X](_ : _ =  \rsum_(i0 | size (f i0) == i)
      Pf (f i0)); last first.
  apply:eq_bigl=>a. 
  rewrite inE.
  apply/eqP/eqP; last by move->.
  by move/INR_eq.
  rewrite -(big_map f (fun i0 => size i0 == i) (fun x => Pf x)) /=.
  rewrite [X in X = _](_ : _ =  \rsum_(i0 | (i0 \in [finType of i.-tuple bool])
  && (tval i0 \in codom f)) Pf i0); last first.
    rewrite big_mkcondr /= .
    apply:eq_bigr=>a _.
    rewrite /Pf.
    case:(pickP _)=>x; first by move/eqP <-; rewrite codom_f.
    by case:ifP.
  by rewrite -big_seq_tuple //; last apply: (dist_support_not_empty P).
rewrite -[X in _ = _ + X]mul1R -distPf big_distrl/= -big_split/=.  
apply:eq_bigr=>? _; by rewrite Rmult_plus_distr_l.
Qed.

Lemma entropy_l5 : `H P <= \rsum_(m| m \in [set x : I_lmax | Ndist x != 0]) 
(Ndist m * INR m) + `H Ndist.
Proof.
rewrite entropy_l4 addRC (addRC _ (`H _)). 
apply:Rplus_le_compat_l.
apply:Rle_big_P_f_g=>i.
rewrite inE; move/eqP=>H.
apply:Rmult_le_compat_l; first by apply:le_0_Pr.
have Rle0Pf:  forall (a:[finType of i.-tuple bool]), 0 <= Pf a / Ndist i.
  move=>a. 
  apply:(Rmult_le_reg_r (Ndist i)).
    apply:Rlt_le_neq; first by apply:le_0_Pr.
    by apply:nesym.
  rewrite mul0R /Rdiv -mulRA -Rinv_l_sym // mulR1.
  rewrite /Pf; case:pickP=>[? _ | ? ]; first by apply:Rle0f.
  by apply:Rle_refl.
pose pmf_Pf := mkPosFun Rle0Pf.
have pmf1_Pf : \rsum_(a | a \in [finType of i.-tuple bool]) pmf_Pf a = 1.
  rewrite /pmf_Pf/=.
  rewrite /Rdiv -big_distrl /=.
  apply:(Rmult_eq_reg_r (Pr[(Top.X P f) = (INR i)]))=>//.
  rewrite -mulRA -Rinv_l_sym // mul1R mulR1 /@pr /Pr /=.
  rewrite [X in _ = X](_ : _ =  \rsum_(i0 | i0 \in [set x | INR (size (f x)) == INR i]) Pf (f i0)); last first.
    apply:eq_bigr=>a ain.
    rewrite /Pf.
    have -> : [pick x | f x == f a ] = Some a; last by[].
      case:pickP; first by move=>x /eqP/ f_inj ->.
      by move/(_ a); rewrite eqxx.
   rewrite [X in _ = X](_ : _ =  \rsum_(i0 | size (f i0) == i)
      Pf (f i0)); last first.
  apply:eq_bigl=>a. 
  rewrite inE.
  apply/eqP/eqP; last by move->.
  by move/INR_eq.
  rewrite -(big_map f (fun i0 => size i0 == i) (fun x => Pf x)) /=.
  rewrite [X in X = _](_ : _ =  \rsum_(i0 | (i0 \in [finType of i.-tuple bool])
  && (tval i0 \in codom f)) Pf i0); last first.
    rewrite big_mkcondr /= .
    apply:eq_bigr=>a _.
    rewrite /Pf.
    case:(pickP _)=>x; first by move/eqP <-; rewrite codom_f.
    by case:ifP.
  by rewrite -big_seq_tuple //; last apply: (dist_support_not_empty P).
pose distPf := mkDist pmf1_Pf.
move:(entropy_max distPf).
rewrite card_tuple/= card_bool -INR_pow_expn log_pow (_ : INR 2 = 2)//.
  by rewrite log_2 mulR1.
by apply:Rlt_R0_R2.
Qed.

Lemma entropy_l6 :  `H P <= `E X + `H Ndist.
Proof.
rewrite (_ :`E X = \rsum_(m| m \in [set x : I_lmax | Pr[X = INR x] != 0]) (Ndist m * INR m)).
by apply:entropy_l5.
rewrite Ex_ord.
rewrite [X in X = _](_:_ = \rsum_(m | m \in [set : I_lmax]) INR m * Ndist m); last first.
  by apply:eq_bigl=>i; rewrite in_setT.
rewrite (rsum_union _ _ _ _ disjoint_0 setU_0).
rewrite [X in _ + X = _](_ :_ = 0). 
  by rewrite addR0; apply:eq_bigr=>i _; rewrite mulRC.
apply:esym; apply: Req_0_rmul=>i.
rewrite inE /Ndist /=.
by move/eqP->; rewrite mulR0.
Qed.

Lemma entropy_l7 : `H P <= `E X + log ((exp 1) * (`E X)).
Proof. 
apply:(Rle_trans _ _ _ entropy_l6).
have X_pos: forall x, 0 < X x .
  move=> x.
  apply:Rlt_le_neq=>//.
  rewrite (_ : 0 = INR 0)//; apply:le_INR.
  by apply:le_0_n.
apply:Rplus_le_compat_l.
rewrite mulRC log_mult; last first.
  by apply:exp_pos.
  move/le_1_Ex:X_pos=>H.
  by apply:(Rlt_le_trans _ _ _ Rlt_0_1).
apply:(le_HN_logE_loge X_pos).
Qed.

End converse_pre.

Section converse'.
Variable A : finType.
Variable P : dist A.
Variable n : nat.
Variable f : n.-tuple A -> seq bool.
Let I_lmax := I_lmax f.
Let X := X (P `^ n) f.
Let Ndist := Ndist (P `^ n) f.
Hypothesis f_uniq : uniquely_decodable _ f.
Hypothesis n_non0 : 0 <> (INR n). (*not required?*) 

Lemma X_non0 x : 0 <> X x.
Proof.
rewrite /X/= /ell.
case:(Req_dec 0 (INR (size (f x))))=>// H.
move:f_uniq.
rewrite /uniquely_decodable/extension /injective=>tmp.
move:H.
rewrite (_ : 0 = INR 0)//; move/INR_eq.
move/esym/size0nil=>fx_nil.
move:(tmp [::] ([:: x])).
rewrite /flatten /= fx_nil cat0s=>H.
have nil: [::] = [::] by[].
by move:(H (nil bool)).
Qed.

Lemma le_entropy_Ex_HN : `H (P `^ n) <= `E X + log ((exp 1) * (`E X)).
Proof.
have f_inj: injective f.
  move=>x1 x2.
  move:f_uniq.
  move/(_ [:: x1] [:: x2]). 
  rewrite /extension /= !cats0=>H1.
  move/H1; by case.
by move:(entropy_l7 f_inj X_non0).
Qed.

Lemma converse1 : `E X < (INR n) * (log (INR #|A|)) -> 
`E X / (INR n) >= `H P - log ((exp 1) * (INR n) * (log (INR #|A|))) / (INR n).
Proof.
move=>H.
apply:Rle_ge.
apply:(Rmult_le_reg_r (INR n)).
  by apply:Rlt_le_neq=>//; rewrite (_ : 0 = INR 0)//; apply:(le_INR _ _ (le_0_n n)).
rewrite /Rminus Rmult_plus_distr_r /Rdiv.
rewrite Ropp_mult_distr_l_reverse -mulRA -(mulRA (`E X)) -Rinv_l_sym; last by apply:nesym.
rewrite !mulR1 mulRC -entropy_TupleDist.
apply:(Rplus_le_reg_r (log (exp 1 * INR n * log (INR #|A|)))).
rewrite -addRA Rplus_opp_l addR0.
apply:(Rle_trans _ _ _ le_entropy_Ex_HN).
apply:Rplus_le_compat_l.
apply:log_increasing_le.
  apply:(Rmult_lt_0_compat _ _ (exp_pos 1)).
  have X_pos :forall x, 0 < X x .
    move=>x.
    apply:Rlt_le_neq; last by apply:X_non0.
    rewrite (_ : 0 = INR 0)//; apply:le_INR.
    by apply:le_0_n.
  move/le_1_Ex:X_pos=>?.
  by apply:(Rlt_le_trans _ _ _ Rlt_0_1).
rewrite -mulRA; apply:Rmult_le_compat_l; first by apply:Rlt_le; apply:exp_pos.
by apply:Rlt_le.
Qed.

Lemma converse2 :  (INR n) * (log (INR #|A|)) <= `E X -> 
`E X / (INR n) >= `H P.
Proof.
move=> H.
apply:Rle_ge.
have n_pos :  0 < INR n.
  by apply:Rlt_le_neq=>//; rewrite (_ : 0 = INR 0)//; apply:(le_INR _ _ (le_0_n n)).
apply:(Rmult_le_reg_r (INR n))=>//.
rewrite mulRC  /Rdiv -mulRA -Rinv_l_sym; last by apply:nesym.
rewrite mulR1; apply:(Rle_trans _ _ _ _ H).
apply:(Rmult_le_compat _ _ _ _ _ (entropy_pos P) (Rle_refl (INR n)) (entropy_max P)).
by apply:Rlt_le.
Qed.

End converse'.

Section converse.
Variable A : finType.
Variable P : dist A.
Variable n : nat.
Variable f : n.-tuple A -> seq bool.
Let I_lmax := I_lmax f.
Let X := X (P `^ n) f.
Let Ndist := Ndist (P `^ n) f.
Hypothesis f_uniq : uniquely_decodable _ f.
Hypothesis n_non0 : 0 <> (INR n). (*not required?*) 

Variable m:nat.
Hypothesis m_non0 : 0 <> (INR m).
Definition fm (x : (m.-tuple [finType of (n.-tuple A)])) := flatten (map f x).

Lemma fm_inj : injective fm.
Proof.
move=>x1 x2 H.
by apply:val_inj; apply:f_uniq.
Qed.

(* Galois connection *)

Lemma fm_uniq : uniquely_decodable _ fm.
Proof.
pose m' := m.-1.
have mpos: m = m'.+1.
  case/Rdichotomy:m_non0; first by rewrite (_ : 0 = INR 0)//; move/INR_lt/(S_pred _ 0).
  by rewrite (_ : 0 = INR 0)//; move/Rgt_lt/INR_lt/ltP.
have: extension [finType of n.-tuple A] f \o (flatten \o map (@tval m _)) =1 extension [finType of m.-tuple [finType of n.-tuple A]] fm.
   by elim => //= ta sta'; rewrite /extension /fm /= map_cat flatten_cat => <-.
apply: eq_inj. apply: inj_comp => //.
rewrite mpos.
 elim => /= [| ta1 sta1 IHsta1]; case => [| ta2 sta2] //=.
 - by case: (tupleP ta2).
 - by case: (tupleP ta1).
 - move/eqP. rewrite eqseq_cat; last by rewrite !size_tuple.
   by move/andP => [/eqP /val_inj -> /eqP /IHsta1 ->].
Qed.

Check (converse1 fm_uniq m_non0).

Let Pm := P `^ n.
Definition Xm := mkRvar (Pm `^ m) (fun x => INR (size (fm x))).

Lemma converse: `E Xm < (INR m) * (log (INR #|[finType of n.-tuple A]|)) -> 
`E Xm / (INR m) >= `H Pm - log ((exp 1) * (INR m) * (log (INR #|[finType of n.-tuple A]|))) / (INR m).
Proof.
by apply:converse1;first apply:fm_uniq.
Qed.

Lemma Ex_m : `E Xm = (INR m) * `E X.
Proof.
rewrite /Ex_alt /Xm /= /ell /fm /TupleDist.f /Pm. 
elim:m=>[| m']; first by rewrite rsum_0tuple /= !mul0R.
elim:m'=>[_ |m'' _ IH].
  rewrite mul1R. rewrite -/(Ex_alt X).
  rewrite -E_rvar2tuple1.
  apply:eq_bigr=>i _.
  rewrite /= /TupleDist.f big_ord_recl big_ord0 mulR1.
  apply:Rmult_eq_compat_r.
  case:(tupleP i)=> ? ?; by rewrite tuple0 /= theadE cats0.
pose fm2 (x :[finType of ((m''.+2).-tuple [finType of (n.-tuple A)])]) := flatten (map f x).
pose Xm2 := mkRvar (Pm `^ (m''.+2)) (fun x => INR (size (fm2 x))).
pose fm1 (x :[finType of ((m''.+1).-tuple [finType of (n.-tuple A)])]) := flatten (map f x).
pose Xm1 := mkRvar (Pm `^ (m''.+1)) (fun x => INR (size (fm1 x))).
have X_Xm1_Xm2: Xm2 \= X \+ Xm1.
  apply:conj=>[|x /=]; first by apply:joint_prod_n.
  rewrite  -plus_INR plusE -size_cat.
  case:(tupleP x)=> ? ?; by rewrite theadE.      
rewrite -/(Ex_alt Xm2) (E_linear_2 X_Xm1_Xm2) -(mul1R (`E X)).
by rewrite /Ex_alt IH -Rmult_plus_distr_r addRC -addn1 S_INR.
Qed.

End converse.

Section vscode_converse.

Variable A : finType.
Variable P : dist A.
Variable n' : nat.
Let n := n'.+1.

Theorem vscode_converse :
  forall (f : var_enc A n), uniquely_decodable _ f ->
  exp_len_cw f P / INR n >= `H P.
Proof.
move=>f f_uniq.
apply:Rle_ge.
apply:le_epsilon=>eps epspos.




%%%%%%%%%%%%%%%%%%%%%%%%%%%%