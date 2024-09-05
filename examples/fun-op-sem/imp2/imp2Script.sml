
open HolKernel Parse boolLib bossLib;
open stringLib integerTheory;
open listTheory;
open arithmeticTheory;
open impTheory;
val ect = BasicProvers.EVERY_CASE_TAC;

val _ = new_theory "imp2";


val _ = temp_type_abbrev("vname",``:string``);

(* make a wellformedness for argument names being distinct...a condition for it in the proof... *)

Datatype:
    com = Assign vname imp$aexp
        | If imp$bexp (com list) (com list)
        | While imp$bexp (com list)
End

val com_size_def = fetch "-" "com_size_def";

Definition imp2imp2_def:
    (imp2imp2 (SKIP:imp$com) = []) /\
    (imp2imp2 (Assign v a) = [((Assign v a):com)]) /\
    (imp2imp2 (Seq c1 c2) = (imp2imp2 c1) ++ (imp2imp2 c2)) /\
    (imp2imp2 (If b c1 c2) = [(If b (imp2imp2 c1) (imp2imp2 c2))]) /\
    (imp2imp2 (While b c) = [(While b (imp2imp2 c))])
End

Theorem com_lt:
    !c h t. MEM c t ==> com_size c < com1_size (h::t)
Proof
    rw[] >>
    simp[com_size_def] >>
    Induct_on `t` >>
    rw[] >>
    simp[com_size_def] >>
    fs[]
QED

Theorem com_ineq:
    !c cs. MEM c cs ==> com_size c <= com1_size cs
Proof
    rw[] >>
    simp[LESS_OR_EQ] >>
    Cases_on `cs` >>
    fs[MEM]
        >- simp[com_size_def]
        >- simp[com_lt]
QED

Definition cval_def:
    (cval 0 _ _ = NONE) /\
    (cval (t:num) (Assign v a) s = SOME ((v =+ aval a s) s)) /\
    (cval t (If b cs1 cs2) s = FOLDL (\os c. (case os of
        | NONE => NONE
        | SOME s' => cval t c s'
    )) (SOME s) (if bval b s then cs1 else cs2)) /\
    (cval t (While b cs) s =
        if bval b s then
        FOLDL (\os c. (case os of
            | NONE => NONE
            | SOME s' => cval (t-1) c s'
        )) (SOME s) (cs ++ [(While b cs)])
        else NONE)
Termination
    WF_REL_TAC `inv_image (measure I LEX measure com_size) (λ(t,c,s). (t,c))` >>
    rw[] >>
    irule LESS_EQ_LESS_TRANS >>
    irule_at Any com_ineq >>
    first_assum $ irule_at Any >>
    simp[]
End

Definition pval_def:
    (pval 0 _ _ = NONE) /\
    (pval t cs s = FOLDL (\os code. (case os of
        | NONE => NONE
        | SOME s' => cval t code s'
    )) (SOME s) cs)
End

Theorem foldl_concat_redundant_l:
    !l. (!l1 l2 s f. l = (l1 ++ l2) ==> FOLDL f s l = FOLDL f (FOLDL f s l1) l2) 
Proof
    Induct_on `l1` (* inducting on l1 as it more matches the structure of ++ ??? *)
        >- simp[]
        >- rw[]
QED

Theorem foldl_concat_aux:
    (!l1 l2 s f. FOLDL f s (l1 ++ l2) = FOLDL f (FOLDL f s l1) l2) 
Proof
    Induct_on `l1` (* inducting on l1 as it more matches the structure of ++ ??? *)
        >- simp[]
        >- rw[]
QED

Theorem foldl_concat:
    FOLDL f s (l1 ++ l2) = FOLDL f (FOLDL f s l1) l2
Proof
    simp[foldl_concat_aux]
QED

Theorem foldl_none:
    FOLDL (λos code. case os of NONE => NONE | SOME s' => cval (SUC n) code s') NONE l = NONE
Proof
    Induct_on `l`
        >- simp[]
        >- simp[FOLDL]
QED

(* STUCK ON THIS *)
(* CVAL here is from this file, not impScript *)
Theorem cval_idemp:
    !t c s t'. t <= t' /\ cval t c s <> NONE ==> cval t c s = cval t' c s 
Proof
    recInduct cval_ind >>
    rw[] >>
    Cases_on `t'` >>
    TRY (fs[cval_def] >> NO_TAC)
        >- (simp[cval_def] >>
            Induct_on `cs1`
                >- rw[]
                >- (rw[]
                    first_x_assum $ qspecl_then [`h`, `s`] assume_tac >>
                    rw[] >>
                    first_x_assum $ qspec_then `SUC n` assume_tac >>
                    Cases_on `cval (SUC v5) h s`
                        >- (rfs[cval_def] >>
                            fs[] >>
                            fs[foldl_none]
                        )
                        >- (gs[] >>
                            gvs[FOLDL]
                            qpat_x_assum `!` mp_tac 

                        )
                    fs[cval_def] >>
                    rfs[]
                )

        ) 
QED

(* IGNORE STUFF BELOW... *)

(* try rephrase the statement *)
(* PLEASE IGNORE *)
Theorem pval_test:
    (pval t cs s <> NONE /\ t <= t') ==> (pval t cs s = pval t' cs s)
Proof
    Cases_on `t` >>
    Cases_on `t'`
        >- simp[pval_def]
        >- simp[pval_def]
        >- simp[pval_def]
        >- (
        (* >- (simp[pval_def] >> *)
            (* qid_spec_tac `s` *)

            (* qid_spec_tac `s` *)
            MAP_EVERY qid_spec_tac [`s` `cs`] >> (* rightmost is outermost quantifier...whoops type error...double check syntax *)
            qid_spec_tac `s` >> (* should I induct on s or cs here...maybe s??? ...s is a function....doesn't have an induction principle defined for it*)
            (* maybe not induct on n but have more generality of them *)
            (* Induct_on `n` >>
            Induct_on `n'` >> *)
            qid_spec_tac `n` >>
            qid_spec_tac `n'` >>
            Induct_on `cs`
                >- rw[pval_def]
                >- (rw[] >>
                    simp[pval_def] (* this looks like a pretty good position...I think I need a monotonicty lemma on cval *)

                )

                >- rw[pval_def]
                >- rw[pval_def]
                >- rw[pval_def]
                >- (fs[pval_def] >>
                    rw[] >>

                )


                >- rw[pval_def]
                >- (fs[pval_def] >>
                    rw[] >>


                )
            
            
            
            rw[] >>
            Induct_on `cs`
                >- rw[]
                >- (rw[] >>
                    gvs[cval_def, FOLDL]
                )
        )
        
        
        >- fs[pval_def]
        >- fs[pval_def]
        >- (simp[pval_def] >>
            gvs[cval_def, FOLDL]
        )
        >- (fs[pval_def] >> (* not enough to prove *)
            gvs[cval_def, FOLDL]
        )
    
    
    rw[] >>

    Induct_on `cs` >>
    rw[]

    Induct_on `cs`
        >- (rw[] >>
            Cases_on `t` >>
            Cases_on `t'`
                >- fs[pval_def]
                >- fs[pval_def]
                >- fs[]
                >- simp[pval_def]
        )
        >- (rw[]

        )

QED



Theorem pval_tmp_idemp:
    !cs. (!t s t'. (pval t cs s <> NONE /\ t <= t') ==> (pval t cs s = pval t' cs s))
Proof
    Induct
        >- (Cases_on `t` >>
            Cases_on `t'` >>
            rw[] 
            simp[pval_def]
        )    
QED


(* gets to a goal that I don't think is provable *)
(* should probably prove the fold directly for easier induction, and then use it to prove this absttraction *)
(* some general things about invariants under folds.... that could potentially be used*)

Theorem pval_tmp_idemp:
    !t cs s t'. (pval t cs s <> NONE /\ t <= t') ==> (pval t cs s = pval t' cs s)
Proof
    (* recInduct pval_ind >> (* effectively a case split since not recursive *)
    rw[]
        >- fs[pval_def]
        >- (Induct_on `cs` >>
            Cases_on `t'` >>
            rw[]
                >- fs[]
                >- simp[pval_def]
                >- fs[]
                >- gvs[pval_def] 
                (* damn, I think inductive hypothesis for pval got instantiated too early??? *)

            Cases_on `t` >>
            Cases_on `t'` >>
            rw[]

        ) *)
    Induct_on `cs` >>
    Cases_on `t` >>
    Cases_on `t'` >>
    rw[]
        >- fs[pval_def]
        >- simp[pval_def]
        >- fs[pval_def]
        >- (* don't think this subgoal is provable...can't proceed ...or do I need to use FOLDL for simplifiers???...pretty sure I need inducive hypothesis for pval....nested induction...which one should be outer...which should be inner?? *)
        (gvs[pval_def, FOLDL]
            (*  *)
        )
QED

(* WANT THIS: FOLDL <the thing> v cs <> NONE ==> v <> NONE *)
            (* WANT THIS TOO: cval n h s <> NONE /\ n <= n' ==> cval n' h s = cval n h s *)
            (* want to get out the same state *)
            (* and also massge the induction hypothesis ...pval *)



(* didn't make much progress with any of these attempts from before *)
    (* Induct
        >- rw[]
        >- (rw[])

        >- (Cases_on `l1`
            >- simp[]
            >- (rw[])
        ) *)


Theorem pval_concat2:
    !t l s l1 l2. l = (l1 ++ l2) ==> pval t (l1 ++ l2) s = OPTION_BIND (pval t l1 s) (pval t l2)
Proof
    ho_match_mp_tac pval_ind >>
    rw[]
        >- simp[pval_def]
        >- (Cases_on `l1`
            >- simp[pval_def]
            >- (simp[pval_def] >>
            )
        )
QED

(* probably need to do induction on l here *)
(* might need explicit quantification ...in which case might need explicit quantification of all the terms*)



Theorem foldl_none_test:
    !l. FOLDL (λos code. case os of NONE => NONE | SOME s' => cval (SUC n) code s') NONE l = NONE
Proof
    Induct
        >- simp[FOLDL]
        >- (strip_tac >>
            rewrite_tac[FOLDL]

        )
    
    rw[] >>
    gen_tac
QED

(* express as a more natural induction on lists *)
(* Theorem pval_concat2: *)

(* if want to use induction theorems *)
(* use c instead of l1 l2 and later do an implication guard to say c = l1 ++ l2 *)
(* want it true for all l1 l2 that equal c...not existential *)
Theorem pval_concat:
    ! t l1 l2 s. pval t (l1 ++ l2) s = OPTION_BIND (pval t l1 s) (pval t l2)
Proof
    rw[] >>
    Cases_on `t`
        >- simp[pval_def]
        >- (Induct_on `l1`
            >- simp[pval_def]
            >- (simp[pval_def]
            )
        )

QED

(* copying the proof because I can't access the existing one *)
(* could just cheat this because I know it already exists *)

Theorem clk_bnd:
    !c s t s' t'. (cval c s t = SOME (s',t')) ==> t' <= t
Proof
    cheat
QED

    recInduct impTheory.cval_ind >>
    rw[]
        >- fs[impTheory.cval_def]
        >- fs[impTheory.cval_def]
        >- (fs[impTheory.cval_def] >>
            Cases_on `cval c1 s t`
                >- fs[]
                >- (fs[] >>
                )

            first_x_assum $ qspec_then `s'` (qspec_then `t'` assume_tac) >> rw[]

        )
QED


(* need t2 to be universally quantified *)
(* i.e. for every t2 it we could get...it is >= t1 .... depends on other stuff??? *)
(* need to quantify all of them because they depend on stuff???? *)
(* actually not sure...still get the same stuff...wth *)
(* pretty sure has to be completely quantified....otherwise saying the wrong thing *)
(* pretty sure t2 has to be existentially quantified *)

Theorem lrg_clk:
    !c s t t' s1 t1. ((t <= t') /\ (cval c s t = SOME (s1, t1))) ==> (?t2.(cval c s t' = SOME (s1, t2)) /\ t1 <= t2)
Proof
    recInduct impTheory.cval_ind >>
    rw[]
        >- (qexists `t'` >> fs[impTheory.cval_def])
        >- (qexists `t'` >> fs[impTheory.cval_def])
        >- (Cases_on `cval c1 s t` >>
            Cases_on `cval c1 s t'`
                >- fs[impTheory.cval_def]
                >- fs[impTheory.cval_def]
                >- (Cases_on `x` >> first_x_assum $ qspecl_then [`t'`, `q`, `r`] assume_tac >> gs[])
                >- (Cases_on `x` >>
                    Cases_on `x'` >>
                    simp[impTheory.cval_def] >>
                    rw[] >> (* this rw automated the instantion I was doing manually...huh???? *)
                    first_x_assum $ qspec_then `t'` assume_tac >>
                    gvs[] >> (* this automatically gave me r <= r' which I want *)
                    first_x_assum $ qspecl_then [`r'`, `s1`, `t1`] assume_tac >>
                    fs[impTheory.cval_def] (* automation doing a lot of the tedious steps...might have been able to do more automation earlier *)
                )
        )
        >- (simp[impTheory.cval_def] >>
            first_x_assum $ qspecl_then [`t'`, `s1`, `t1`] assume_tac >>
            rfs[impTheory.cval_def]
        )
        >- (simp[impTheory.cval_def] >>
            first_x_assum $ qspecl_then [`t'`, `s1`, `t1`] assume_tac >>
            rfs[impTheory.cval_def]
        )
        >- (Cases_on `t` >>
            Cases_on `bval b s`
                >- fs[Once impTheory.cval_def] (* need once otherwise it loops *)
                >- fs[Once impTheory.cval_def]
                >- (gvs[] >>
                    first_x_assum $ qspecl_then [`t'-1`, `s1`, `t1`] assume_tac >>
                    fs[Once impTheory.cval_def] >>
                    Cases_on `cval c s n`
                        >- fs[Once impTheory.cval_def]
                        >- (Cases_on `x` >> gvs[Once impTheory.cval_def])
                )
                >- fs[Once impTheory.cval_def]
        )
QED

(* should s1 t1 s2 t2 be quantified???? *)
(* should anything be quantified *)
(* the states should actually be equal as well but weakening the statement so easier to just show for clocks *)
(* might not actually be easier tbh...a stronger statement gives more assumptions to be exploited *)
(* because might not actually be true unless s1 = s2 *)
(* so might need this information to be present in the induction hypothesis...lets see how far I get....just replace s2 with s1??? *)
Theorem clk_mono:
    !c s t t'. ((t <= t') /\ (cval c s t = SOME (s1, t1))) ==> ((cval c s t' = SOME (s2, t2)) /\ t1 <= t2)
Proof
    recInduct impTheory.cval_ind >>
    rw[]
        >- 
QED

(* need a temporal idempotence lemma on impTheory.cval*)
(* or at the very least...want one *)
(* need the FST...so is this actually useful???? *)

Theorem tmp_idemp:
    !c s t t'. ((t <= t') /\ (cval c s t <> NONE)) ==> (OPTION_MAP FST (cval c s t)) = (OPTION_MAP FST (cval c s t'))
Proof
    recInduct impTheory.cval_ind >>
    rw[]
        >- simp[impTheory.cval_def]
        >- simp[impTheory.cval_def]
        >- (Cases_on `cval c1 s t` >>
            Cases_on `cval c1 s t'`
            >- fs[impTheory.cval_def]
            >- fs[impTheory.cval_def]
            >- (first_x_assum $ qspec_then `t'` assume_tac >> rfs[]) (* rfs worked but fs didn't. gs and gvs also worked...I guess needed reverse... *)
            >- ((*assume_tac clk_bnd >>*) (* maybe drule rather than assume *)
                Cases_on `x` >> (* is this a hack?? *)
                Cases_on `x'` >>
                rw[]
                simp[impTheory.cval_def] (* I think I need a lemma to relate r and r' but that feels just as complicated as proving this...feels like things will get a bit circular?? *)


                drule clk_bnd >>
                rw[] >>
                drule clk_bnd

                last_x_assum $ qspec_then `q` (qspec_then `r` assume_tac)
                rw[]
                first_x_assum $ qspec_then `t'` assume_tac
                (* rw[] >> *)
                simp[impTheory.cval_def]


                last_x_assum $ qspec_then `t'` assume_tac >>
                gvs[] >>
                Cases_on `x >>
                simp[impTheory.cval_def]
                assume_tac
            )
            
            simp[impTheory.cval_def] >>
            Cases_on `cval c1 s t`
                >- fs[impTheory.cval_def]
                >- ()
        )
QED

(* is this actually true...they might timeout at different times *)
(* maybe should say only true if don't both timeout *)
(* pretty sure imp2 can't timeout before imp *)

(* think part of the problem is t...no reason for them to share the same clock *)
(* in general things won't share quantifiers *)
(* but I'm pretty sure this is actually a true statement *)
(* might have to be a corollary of a simpler lemma where they have separate quantifiers *)
Theorem equiv_lang:
    !c s t. (OPTION_MAP FST (cval c s t) <> NONE) /\ ((pval t (imp2imp2 c) s) <> NONE) ==> OPTION_MAP FST (cval c s t) = pval t (imp2imp2 c) s
Proof
    ho_match_mp_tac impTheory.cval_ind >>
    rw[] >>
    Cases_on `t` >>
    TRY (fs[pval_def] >> NO_TAC)
        >- simp[impTheory.cval_def, imp2imp2_def, pval_def]
        >- simp[impTheory.cval_def, imp2imp2_def, pval_def, cval_def]
        >- (Cases_on `cval c s (SUC n)` >>
            Cases_on `pval (SUC n) (imp2imp2 c) s`
                >- fs[impTheory.cval_def]
                >- fs[impTheory.cval_def]
                >- (fs[pval_def] >>
                    fs[imp2imp2_def] >>
                    fs[foldl_concat] >>
                    fs[foldl_none]
                )
                >- (rw[] >>
                    simp[impTheory.cval_def] >>
                    simp[imp2imp2_def] >>
                    simp[pval_def] >>
                    simp[foldl_concat] >>
                    fs[pval_def] >>
                    Cases_on `x` >>
                    simp[] >>
                    assume_tac lrg_clk >>
                    (* qspecl_then [``] *)
                    assume_tac clk_bnd >>

                    (*gvs[]*) (* gvs maybe more powerful than what is need...change to least powerful tactic ....don't want it to instantiate the quantifiers*)
                    (* think I proved a slightly less helpful lemma *)
                    (* would have been better to prove it for pval rather than cval *)
                    (* can still salvage things *)
                    (* I think just easier if prove tmp idempotence for pval *)


                    (* first get an instantiated version of the universally quantified assumption *)
                    (* s' should equal x' *)
                    (* t' should equal SUC n *)
                    first_x_assum $ qspec_then `x'` (qspec_then `SUC n` assume_tac) 
                    simp[impTheory.cval_def] >>
                    simp[imp2imp2_def] >>
                    simp[pval_def] >>
                    simp[foldl_concat] >>
                    fs[] >> (* I don't think I have enough information...not necessarily SUC n for impTheory *)
                    
                    
                    Cases_on `t2 = SUC n`
                        >- (gvs[]
                        )
                    fs[pval_def] >>
                    Cases_on `x` >>
                )

                >- fs[impTheory.cval_def]
                >- (Cases_on `pval (SUC n) (imp2imp2 c) s`
                        >- fs[pval_def, impTheory.cval_def, cval_def, imp2imp2_def]
                        Cases_on `x` >>
                        gvs[] >>
                        simp[pval_def] >>
                        simp[imp2imp2_def]
                    )
            )
        
        
        >- (fs[impTheory.cval_def]
            
            gvs[impTheory.cval_def] >>
            gvs[imp2imp2_def] >>
            gvs[pval_def]


            (* Cases_on `cval c s (Suc n)` *)
                >- (gvs[imp2imp2_def]
                    fs[impTheory.cval_def] >>
                    rfs[]
                )
        ) 
    (* TRY (simp[impTheory.cval_def, imp2imp2_def, pval_def, cval_def] >> NO_TAC)
    simp[impTheory.cval_def, imp2imp2_def, pval_def, cval_def] *)
QED

