/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ffcf1867-1f61-4ffa-989e-3920c4fe53bf

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

/-
Formalization of the Immerman-Szelepcsényi theorem (NL = coNL). We prove that if a nondeterministic space-bounded machine exists that can verify the Immerman witness (which we prove correctly characterizes non-reachability), then NSPACE is closed under complementation. We formally prove the correctness of the counting argument and the witness structure, covering all the logical steps of the proof including the inductive counting lemma and the equivalence of the witness condition with non-reachability. The explicit construction of the Turing Machine is omitted but its existence is the only conditional hypothesis.
-/

import Mathlib


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

set_option linter.mathlibStandardSet false

open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

#check Turing.Dir

/-
Definitions of Turing Machine, Configuration, Step, Reachability, Acceptance (N and co-N), and Space Boundedness.
-/
inductive Move
| Left
| Stay
| Right
deriving DecidableEq, Repr

def Move.toInt : Move → Int
| Move.Left => -1
| Move.Stay => 0
| Move.Right => 1

structure TuringMachine (k : ℕ) (σ : Type) where
  V : Type
  [decV : DecidableEq V]
  [fintypeV : Fintype V]
  edges : Set (V × V × (Fin k → σ) × (Fin (k-1) → σ) × (Fin k → Move))
  startState : V
  acceptState : V
  rejectState : V

structure Configuration (k : ℕ) (σ : Type) (V : Type) where
  state : V
  tapes : Fin k → ℕ → σ
  positions : Fin k → ℤ

variable {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]

def step (M : TuringMachine k σ) (c : Configuration k σ M.V) (c' : Configuration k σ M.V) : Prop :=
  ∃ (r : Fin k → σ) (w : Fin (k-1) → σ) (m : Fin k → Move),
    (c.state, c'.state, r, w, m) ∈ M.edges ∧
    (∀ i, c.tapes i (c.positions i).toNat = r i) ∧
    (∀ i : Fin (k-1),
      let idx : Fin k := ⟨i.val + 1, by
        grind⟩
      c'.tapes idx (c.positions idx).toNat = w i) ∧
    (∀ i : Fin k, ∀ n, n ≠ (c.positions i).toNat → c'.tapes i n = c.tapes i n) ∧
    (∀ i, c'.positions i = c.positions i + (m i).toInt) ∧
    (∀ n, c'.tapes 0 n = c.tapes 0 n)

def Reachable (M : TuringMachine k σ) (c1 c2 : Configuration k σ M.V) : Prop :=
  Relation.ReflTransGen (step M) c1 c2

def InitialConfig (M : TuringMachine k σ) (input : List σ) : Configuration k σ M.V :=
  { state := M.startState,
    tapes := fun i n =>
      if i = 0 then
        if n < input.length then input.get! n else default
      else default,
    positions := fun _ => 0 }

def AcceptsN (M : TuringMachine k σ) (input : List σ) : Prop :=
  ∃ c, Reachable M (InitialConfig M input) c ∧ c.state = M.acceptState

def Terminal (M : TuringMachine k σ) (c : Configuration k σ M.V) : Prop :=
  ¬∃ c', step M c c'

def AcceptsCoN (M : TuringMachine k σ) (input : List σ) : Prop :=
  ∀ c, Reachable M (InitialConfig M input) c → Terminal M c → c.state = M.acceptState

def SpaceBounded (M : TuringMachine k σ) (S : ℕ → ℕ) : Prop :=
  ∀ input, ∀ c, Reachable M (InitialConfig M input) c →
    ∀ i, (c.positions i).natAbs ≤ S input.length

#check Nat.log2

/-
Definitions for reachability within n steps and the count of such reachable configurations.
-/
def ReachableInAtMost (M : TuringMachine k σ) (c1 c2 : Configuration k σ M.V) (n : ℕ) : Prop :=
  ∃ path : List (Configuration k σ M.V),
    path.length ≤ n + 1 ∧
    path.head? = some c1 ∧
    path.getLast? = some c2 ∧
    path.Chain' (step M)

def ReachableCount (M : TuringMachine k σ) (input : List σ) (n : ℕ) : ℕ :=
  Nat.card { c : Configuration k σ M.V | ReachableInAtMost M (InitialConfig M input) c n }

/-
Lemma: The set of tapes with content bounded by S is finite.
-/
lemma FiniteBoundedTape {σ : Type} [Fintype σ] [Inhabited σ] [DecidableEq σ] (S : ℕ) :
  Set.Finite { t : ℕ → σ | ∀ n, n > S → t n = default } := by
    -- The set of functions `t : ℕ → σ` such that `t n = default` for all `n > S` is in one-to-one correspondence with the set of functions `Fin (S + 1) → σ`.
    have h_bij : {t : ℕ → σ | ∀ n > S, t n = Inhabited.default} = Set.image (fun f : Fin (S + 1) → σ => fun n => if h : n < S + 1 then f ⟨n, h⟩ else Inhabited.default) (Set.univ : Set (Fin (S + 1) → σ)) := by
      ext t;
      constructor;
      · intro ht;
        use fun i => t i;
        grind;
      · grind;
    exact h_bij ▸ Set.toFinite _

/-
Definition of a bounded configuration, where positions are within [-S, S] and tape contents are default outside [0, S] (except for the read-only tape).
-/
def BoundedConfig (M : TuringMachine k σ) (S : ℕ) (input : List σ) (c : Configuration k σ M.V) : Prop :=
  (∀ i, (c.positions i).natAbs ≤ S) ∧
  (∀ n, c.tapes 0 n = if n < input.length then input.get! n else default) ∧
  (∀ i : Fin k, i.val ≠ 0 → ∀ n, n > S → c.tapes i n = default)

/-
Definition of BoundedTapes: tape 0 matches input, other tapes are default outside [0, S].
-/
def BoundedTapes (k : ℕ) [NeZero k] (σ : Type) [Inhabited σ] (S : ℕ) (input : List σ) (ts : Fin k → ℕ → σ) : Prop :=
  (∀ n, ts 0 n = if n < input.length then input.get! n else default) ∧
  (∀ i : Fin k, i.val ≠ 0 → ∀ n, n > S → ts i n = default)

/-
Lemma: The set of bounded tapes is finite.
-/
lemma FiniteBoundedTapes (k : ℕ) (σ : Type) [Fintype σ] [Inhabited σ] [DecidableEq σ] [NeZero k] (S : ℕ) (input : List σ) :
  Set.Finite { ts | BoundedTapes k σ S input ts } := by
    -- By definition of bounded tapes, the set of bounded tapes is isomorphic to a product of finite sets.
    have h_finite_product : {ts : Fin k → ℕ → σ | BoundedTapes k σ S input ts} ⊆ (Set.pi Set.univ fun i : Fin k =>
      if i.val = 0 then
        Set.image (fun t : Fin input.length → σ => fun n => if h : n < input.length then t ⟨n, h⟩ else default) (Set.univ : Set (Fin input.length → σ))
      else
        Set.image (fun t : Fin (S + 1) → σ => fun n => if h : n ≤ S then t ⟨n, by
          exact?⟩ else default) (Set.univ : Set (Fin (S + 1) → σ))) := by
          intro ts hts; simp_all +decide [ BoundedTapes ];
          intro i; split_ifs <;> simp_all +decide [ Set.mem_range ] ;
          · exact ⟨ fun ⟨ n, hn ⟩ => input[n]?.getD Inhabited.default, funext fun n => by aesop ⟩;
          · use fun n => ts i n;
            ext n; aesop;
    exact Set.Finite.subset ( Set.Finite.pi fun i => by split_ifs <;> [ exact Set.toFinite _ ; exact Set.toFinite _ ] ) h_finite_product

/-
Definition of BoundedPositions and lemma stating it is a finite set.
-/
def BoundedPositions (k : ℕ) (S : ℕ) (ps : Fin k → ℤ) : Prop :=
  ∀ i, (ps i).natAbs ≤ S

lemma FiniteBoundedPositions (k : ℕ) (S : ℕ) :
  Set.Finite { ps | BoundedPositions k S ps } := by
    -- Since each individual set is finite, their product is also finite.
    have h_finite : ∀ i : Fin k, Set.Finite {ps_i : ℤ | ps_i.natAbs ≤ S} := by
      exact fun i => Set.Finite.subset ( Set.finite_Icc ( -S : ℤ ) S ) fun x hx => ⟨ by cases abs_cases x <;> linarith [ hx.out ], by cases abs_cases x <;> linarith [ hx.out ] ⟩;
    exact Set.Finite.subset ( Set.Finite.pi fun i => h_finite i ) ( fun ps hps => by aesop )

/-
Definition of BoundedConfigTuples as the product of states, bounded tapes, and bounded positions.
-/
def BoundedConfigTuples (M : TuringMachine k σ) (S : ℕ) (input : List σ) : Set (M.V × (Fin k → ℕ → σ) × (Fin k → ℤ)) :=
  Set.univ ×ˢ ({ ts | BoundedTapes k σ S input ts } ×ˢ { ps | BoundedPositions k S ps })

/-
Lemma: The set of states is finite.
-/
lemma FiniteStates (M : TuringMachine k σ) : Set.Finite (Set.univ : Set M.V) := by
  -- Since the set of states is finite, its cardinality is a natural number.
  have h_card : Finite (Set.univ : Set M.V) := by
    have h_fintype : Fintype M.V := by
      exact M.fintypeV
    exact Set.finite_univ;
  exact h_card

#check @SpaceBounded

#check @AcceptsN

#check @AcceptsCoN

variable {σ : Type} [DecidableEq σ] [Inhabited σ]

def LanguageRecognizedByN {k : ℕ} [NeZero k] (M : TuringMachine k σ) : Set (List σ) :=
  { input | AcceptsN M input }

def LanguageRecognizedByCoN {k : ℕ} [NeZero k] (M : TuringMachine k σ) : Set (List σ) :=
  { input | AcceptsCoN M input }

#check @LanguageRecognizedByN

#check @LanguageRecognizedByCoN

/-
Definitions of NSPACE and co-NSPACE complexity classes.
InNSPACE S L means there exists a k-tape nondeterministic TM M that is S-space bounded and recognizes L.
InCoNSPACE S L means there exists a k-tape co-nondeterministic TM M that is S-space bounded and recognizes L.
-/
variable {σ : Type} [DecidableEq σ] [Inhabited σ]

def InNSPACE (S : ℕ → ℕ) (L : Set (List σ)) : Prop :=
  ∃ (k : ℕ) (hk : NeZero k) (M : TuringMachine k σ), @SpaceBounded k σ _ hk M S ∧ @LanguageRecognizedByN σ _ k hk M = L

def InCoNSPACE (S : ℕ → ℕ) (L : Set (List σ)) : Prop :=
  ∃ (k : ℕ) (hk : NeZero k) (M : TuringMachine k σ), @SpaceBounded k σ _ hk M S ∧ @LanguageRecognizedByCoN σ _ k hk M = L

/-
The set of configurations with space bounded by S is finite.
-/
variable {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]

lemma FiniteBoundedConfig {k : ℕ} [NeZero k] (M : TuringMachine k σ) (S : ℕ) (input : List σ) :
  Set.Finite { c : Configuration k σ M.V | BoundedConfig M S input c } := by
    convert Set.Finite.prod ( FiniteStates M ) ( Set.Finite.prod ( FiniteBoundedTapes k σ S input ) ( FiniteBoundedPositions k S ) ) using 1;
    constructor <;> intro h;
    · convert Set.Finite.prod ( FiniteStates M ) ( Set.Finite.prod ( FiniteBoundedTapes k σ S input ) ( FiniteBoundedPositions k S ) ) using 1;
    · convert h.image _ using 1;
      swap;
      exact fun x => ⟨ x.1, x.2.1, x.2.2 ⟩;
      ext ⟨ state, tapes, positions ⟩ ; unfold BoundedConfig BoundedTapes BoundedPositions; aesop;

/-
Definition of the next configuration given a current configuration and transition details (new state, write values, moves).
This constructs the configuration explicitly.
-/
def NextConfig {k : ℕ} [NeZero k] {V : Type} (c : Configuration k σ V) (q' : V) (w : Fin (k-1) → σ) (m : Fin k → Move) : Configuration k σ V :=
  { state := q',
    tapes := fun i n =>
      if h : i.val = 0 then c.tapes i n
      else if n = (c.positions i).toNat then
        w ⟨i.val - 1, by
          have : i.val < k := i.isLt
          have : i.val ≥ 1 := Nat.pos_of_ne_zero h
          omega⟩
      else c.tapes i n,
    positions := fun i => c.positions i + (m i).toInt }

/-
Characterization of the step relation using NextConfig.
-/
lemma step_eq_NextConfig {k : ℕ} [NeZero k] (M : TuringMachine k σ) (c c' : Configuration k σ M.V) :
  step M c c' ↔ ∃ (r : Fin k → σ) (w : Fin (k-1) → σ) (m : Fin k → Move),
    (c.state, c'.state, r, w, m) ∈ M.edges ∧
    (∀ i, c.tapes i (c.positions i).toNat = r i) ∧
    c' = NextConfig c c'.state w m := by
      constructor;
      · intro h_step
        obtain ⟨r, w, m, h_edge, h_read, h_write, h_tape_pos, h_tape_update⟩ := h_step;
        refine' ⟨ r, w, m, h_edge, h_read, _ ⟩;
        unfold NextConfig;
        congr! 1;
        · ext i n; by_cases hi : i.val = 0 <;> by_cases hn : n = ( c.positions i ).toNat <;> simp +decide [ * ] ;
          · rw [ show i = ⟨ 0, NeZero.pos k ⟩ from Fin.ext hi ] ; aesop;
          · convert h_write ⟨ i - 1, _ ⟩ using 1;
            rcases i with ⟨ _ | i, hi ⟩ <;> norm_num at *;
            contradiction;
        · exact funext h_tape_update.1;
      · rintro ⟨ r, w, m, h₁, h₂, h₃ ⟩;
        refine' ⟨ r, w, m, h₁, _, _, _, _ ⟩;
        · exact h₂;
        · unfold NextConfig at h₃;
          intro i; rw [ h₃ ] ; simp +decide [ Fin.ext_iff ] ;
        · intro i n hn; rw [ h₃ ] ; unfold NextConfig; simp +decide [ hn ] ;
        · exact ⟨ fun i => h₃.symm ▸ rfl, fun n => h₃.symm ▸ rfl ⟩

/-
The set of bounded configuration tuples is finite.
-/
variable {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]

lemma FiniteBoundedConfigTuples {k : ℕ} [NeZero k] (M : TuringMachine k σ) (S : ℕ) (input : List σ) :
  Set.Finite (BoundedConfigTuples M S input) := by
    convert Set.Finite.prod ( FiniteStates M ) ( Set.Finite.prod ( FiniteBoundedTapes k σ S input ) ( FiniteBoundedPositions k S ) ) using 1

/-
Move is a finite type.
-/
instance : Fintype Move :=
  Fintype.ofEquiv (Fin 3)
    { toFun := fun x =>
        if x = 0 then Move.Left
        else if x = 1 then Move.Stay
        else Move.Right
      invFun := fun x =>
        match x with
        | Move.Left => 0
        | Move.Stay => 1
        | Move.Right => 2
      left_inv := by
        decide +revert
      right_inv := by
        -- By definition of right inverse, we need to show that for every x in Fin 3, applying the first function followed by the second function gives back x.
        intro x
        cases x <;> simp +decide [Function.RightInverse] }

/-
The set of edges in the Turing machine is finite.
-/
variable {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]

lemma FiniteEdges {k : ℕ} [NeZero k] (M : TuringMachine k σ) : Set.Finite M.edges := by
  convert Set.toFinite M.edges;
  have := M.fintypeV;
  infer_instance

/-
Helper function that computes the next configuration from a given configuration and an edge tuple.
The edge tuple contains (current state, next state, read values, write values, moves).
This function extracts the necessary components and calls NextConfig.
-/
def EdgeToNextConfig {k : ℕ} [NeZero k] {V : Type} (c : Configuration k σ V)
  (e : V × V × (Fin k → σ) × (Fin (k-1) → σ) × (Fin k → Move)) : Configuration k σ V :=
  NextConfig c e.2.1 e.2.2.2.1 e.2.2.2.2

/-
The set of successor configurations is finite.
-/
variable {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]

lemma FiniteSuccessors {k : ℕ} [NeZero k] (M : TuringMachine k σ) (c : Configuration k σ M.V) :
  Set.Finite { c' | step M c c' } := by
    convert Set.Finite.subset ( Set.Finite.image ( fun e : M.V × M.V × ( Fin k → σ ) × ( Fin ( k - 1 ) → σ ) × ( Fin k → Move ) => EdgeToNextConfig c e ) ( M.edges.finite_coe_iff.mp ( by
      exact Set.Finite.to_subtype <| FiniteEdges M ) ) ) ( show { c' | step M c c' } ⊆ ( Set.image ( fun e : M.V × M.V × ( Fin k → σ ) × ( Fin ( k - 1 ) → σ ) × ( Fin k → Move ) => EdgeToNextConfig c e ) M.edges ) from ?_ ) using 1
    generalize_proofs at *
    generalize_proofs at *;
    intro c' hc'
    obtain ⟨r, w, m, he, hr, hc'⟩ := step_eq_NextConfig M c c' |>.1 hc';
    exact ⟨ _, he, by exact? ⟩

/-
The set of possible next configurations derived from edges is finite.
-/
def NextConfigs {k : ℕ} [NeZero k] (M : TuringMachine k σ) (c : Configuration k σ M.V) : Set (Configuration k σ M.V) :=
  Set.image (EdgeToNextConfig c) M.edges

lemma FiniteNextConfigs {k : ℕ} [NeZero k] (M : TuringMachine k σ) (c : Configuration k σ M.V) :
  Set.Finite (NextConfigs M c) := by
    convert Set.Finite.image _ ( FiniteEdges M ) using 1

/-
The set of configurations reachable in at most n steps, defined recursively, is finite.
-/
def ReachableSet {k : ℕ} [NeZero k] (M : TuringMachine k σ) (input : List σ) : ℕ → Set (Configuration k σ M.V)
| 0 => {InitialConfig M input}
| n + 1 => ReachableSet M input n ∪ ⋃₀ (NextConfigs M '' (ReachableSet M input n))

lemma FiniteReachableSet {k : ℕ} [NeZero k] (M : TuringMachine k σ) (input : List σ) (n : ℕ) :
  Set.Finite (ReachableSet M input n) := by
    induction' n with n ih;
    · exact Set.finite_singleton _;
    · convert ih.union ( ih.biUnion fun c hc => FiniteNextConfigs M c ) using 1;
      ext c; simp [ReachableSet]

/-
If a Turing machine is space-bounded by S, then every reachable configuration is a BoundedConfig (positions within S, tapes default outside S).
-/
lemma SpaceBounded_Implies_BoundedConfig {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hM : SpaceBounded M S) (input : List σ) (c : Configuration k σ M.V) :
  Reachable M (InitialConfig M input) c → BoundedConfig M (S input.length) input c := by
    have h_pos : ∀ c, Reachable M (InitialConfig M input) c → ∀ i, (c.positions i).natAbs ≤ S input.length := by
      exact?;
    intro hc
    unfold BoundedConfig
    constructor
    refine' fun i => h_pos c hc i
    constructor
    generalize_proofs at *;
    · intro n
      induction' hc with c' hc' ih generalizing n
      generalize_proofs at *;
      · unfold InitialConfig; aesop;
      · cases ‹step M c' hc'› ; aesop;
    · intro i hi n hn
      induction' hc with c' c'' hc' hc'' ih generalizing i n
      generalize_proofs at *;
      · unfold InitialConfig; aesop;
      · obtain ⟨ r, w, m, h₁, h₂, h₃, h₄, h₅ ⟩ := hc'';
        by_cases h₆ : n = (c'.positions i).toNat <;> simp_all +decide [ Finset.mem_univ, Set.mem_univ ];
        contrapose! hn;
        exact Int.le_of_lt_add_one ( by linarith [ abs_le.mp ( show |c'.positions i| ≤ S input.length from by linarith [ h_pos c' hc' i ] ) ] )

/-
There exists a Turing machine that accepts all inputs.
-/
lemma Exists_Simple_TM {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ] :
  ∃ (k : ℕ) (hk : NeZero k) (M : TuringMachine k σ), ∀ x, AcceptsN M x ↔ True := by
    refine' ⟨ 1, _, _ ⟩;
    exact ⟨ by norm_num ⟩;
    refine' ⟨ _, _ ⟩;
    use Fin 2;
    exact Set.univ;
    exact 0;
    exact 0;
    exact 0;
    intro x; exact ⟨ fun _ => trivial, fun _ => ⟨ _, Relation.ReflTransGen.refl, rfl ⟩ ⟩ ;

/-
The number of configurations reachable in 0 steps is 1.
-/
lemma ReachableCount_Zero {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) :
  ReachableCount M input 0 = 1 := by
    -- The set {c | ReachableInAtMost M (InitialConfig M input) c 0} is exactly {InitialConfig M input}, so its cardinality is 1.
    have h_singleton : {c : Configuration k σ M.V | ReachableInAtMost M (InitialConfig M input) c 0} = {InitialConfig M input} := by
      ext c; simp [ReachableInAtMost];
      constructor;
      · rintro ⟨ path, hpath₁, hpath₂, hpath₃, hpath₄ ⟩ ; rcases path with ( _ | ⟨ _, _ | path ⟩ ) <;> aesop;
      · rintro rfl; use [InitialConfig M input]; simp +decide ;
        exact List.isChain_singleton _;
    unfold ReachableCount; aesop;

/-
If a configuration is reachable in at most n steps, it is reachable in at most n+1 steps.
-/
lemma ReachableInAtMost_Mono {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (c1 c2 : Configuration k σ M.V) (n : ℕ) :
  ReachableInAtMost M c1 c2 n → ReachableInAtMost M c1 c2 (n + 1) := by
    rintro ⟨ path, hpath₁, hpath₂, hpath₃, hpath₄ ⟩;
    exact ⟨ path, by linarith, hpath₂, hpath₃, hpath₄ ⟩

/-
If c is reachable in at most n steps and c -> c', then c' is reachable in at most n+1 steps.
-/
lemma ReachableInAtMost_Step {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) (c c' : Configuration k σ M.V) (n : ℕ) :
  ReachableInAtMost M (InitialConfig M input) c n → step M c c' →
  ReachableInAtMost M (InitialConfig M input) c' (n + 1) := by
    intro h1 h2
    obtain ⟨path, hpath_len, hpath_head, hpath_last, hpath_chain⟩ := h1
    use path ++ [c'];
    simp_all +decide [ List.isChain_append ];
    -- Since the last element of the path is c and c' is reachable from c, the chain condition holds.
    have h_chain : List.Chain' (step M) (path ++ [c']) := by
      have h_last : path.getLast? = some c := hpath_last
      have h_step : step M c c' := h2
      -- Since the last element of the path is c and c' is reachable from c, the chain condition holds for the appended list.
      have h_chain_append : List.Chain' (step M) (path ++ [c']) := by
        have h_last : path.getLast? = some c := h_last
        have h_step : step M c c' := h_step
        exact List.isChain_append.mpr ⟨hpath_chain, by
          aesop⟩;
      exact h_chain_append;
    exact h_chain

/-
If a configuration is reachable in at most n+1 steps, it is either reachable in at most n steps or it is a successor of a configuration reachable in at most n steps.
-/
lemma ReachableInAtMost_Succ_Imp {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) (c' : Configuration k σ M.V) (n : ℕ) :
  ReachableInAtMost M (InitialConfig M input) c' (n + 1) →
  ReachableInAtMost M (InitialConfig M input) c' n ∨
  ∃ c, ReachableInAtMost M (InitialConfig M input) c n ∧ step M c c' := by
    rintro ⟨ path, h1, h2, h3, h4 ⟩;
    by_cases h_case : path.length ≤ n + 1;
    · exact Or.inl ⟨ path, by linarith, h2, h3, h4 ⟩;
    · -- Since `len = n + 2`, we can split the path into `p'` and `[c']`.
      obtain ⟨p', hp'⟩ : ∃ p', path = p' ++ [c'] ∧ p'.length = n + 1 := by
        exact ⟨ path.dropLast, by rw [ List.dropLast_append_getLast? ] ; aesop, by rw [ List.length_dropLast ] ; omega ⟩;
      -- Since `p'` is a prefix of `path`, it starts at `InitialConfig M input` and ends at some `c`.
      obtain ⟨c, hc⟩ : ∃ c, p'.head? = some (InitialConfig M input) ∧ p'.getLast? = some c ∧ List.Chain' (step M) p' := by
        have h_chain : List.Chain' (step M) p' := by
          rw [hp'.left] at h4;
          exact List.isChain_append.mp h4 |>.1;
        cases p' <;> aesop;
      refine' Or.inr ⟨ c, _, _ ⟩;
      · use p';
        grind;
      · have := List.isChain_append.mp ( by aesop : List.Chain' ( step M ) ( p' ++ [ c' ] ) ) ; aesop;

/-
The set of configurations reachable in n+1 steps is the union of those reachable in n steps and their successors.
-/
lemma ReachableSet_Succ {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) :
  { c | ReachableInAtMost M (InitialConfig M input) c (n + 1) } =
  { c | ReachableInAtMost M (InitialConfig M input) c n } ∪
  { c' | ∃ c, ReachableInAtMost M (InitialConfig M input) c n ∧ step M c c' } := by
    ext cset.antisymm;
    constructor <;> intro h;
    · apply ReachableInAtMost_Succ_Imp M input cset.antisymm n h |> Or.imp (fun h => by
        exact h) (fun h => by
        exact h);
    · -- By definition of union, we can split into two cases.
      cases' h with h_case1 h_case2;
      · -- By definition of ReachableInAtMost, if cset.antisymm is reachable in n steps, then it is also reachable in n+1 steps.
        apply ReachableInAtMost_Mono; assumption;
      · obtain ⟨ c, hc₁, hc₂ ⟩ := h_case2; exact ReachableInAtMost_Step M input c _ _ hc₁ hc₂;

/-
The set of configurations reachable in 0 steps is exactly the singleton set containing the initial configuration.
-/
lemma ReachableInAtMost_Zero {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) :
  { c | ReachableInAtMost M (InitialConfig M input) c 0 } = { InitialConfig M input } := by
    ext c;
    constructor;
    · rintro ⟨ path, hpath₁, hpath₂, hpath₃, hpath₄ ⟩;
      rcases path with ( _ | ⟨ _, _ | path ⟩ ) <;> aesop;
    · rintro rfl;
      use [InitialConfig M input];
      simp [List.Chain']

/-
A set-theoretic lemma: If we know the size N of a finite set {x | P x}, we can prove that c does not satisfy P by exhibiting a subset S of size N where every element satisfies P, and c is not in S.
-/
lemma Set_Card_Certificate_Of_NonMembership {U : Type} (P : U → Prop) [DecidablePred P] (S_P : Set U) (hS_P : S_P = {x | P x}) (hFinite : S_P.Finite) (N : ℕ) (hN : Nat.card S_P = N) (c : U) :
  (¬ P c) ↔ ∃ (S : Set U), S.Finite ∧ Nat.card S = N ∧ S ⊆ S_P ∧ c ∉ S := by
    constructor <;> intro h;
    · exact ⟨ S_P, hFinite, by aesop ⟩;
    · obtain ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩ := h; have := hFinite; have := hS₁; simp_all +decide [ Set.Finite ] ;
      have h_card_eq : Set.ncard S = Set.ncard {x | P x} := by
        convert hS₂ using 1;
      contrapose! h_card_eq;
      refine' ne_of_lt ( Set.ncard_lt_ncard _ _ );
      · exact ⟨ hS₃, fun h => hS₄ <| h h_card_eq ⟩;
      · exact Set.finite_coe_iff.mp hFinite

/-
The set of configurations reachable in at most n steps is finite.
-/
lemma Finite_ReachableInAtMost {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) :
  Set.Finite { c | ReachableInAtMost M (InitialConfig M input) c n } := by
    -- We prove this by induction on n.
    induction' n with n ih;
    · exact Set.Finite.subset ( Set.finite_singleton ( InitialConfig M input ) ) ( by rw [ ReachableInAtMost_Zero ] );
    · convert Set.Finite.union ih ( Set.Finite.biUnion ih fun c hc => FiniteSuccessors M c ) using 1;
      convert ReachableSet_Succ M input n using 1;
      aesop

/-
If we know the number of reachable configurations, we can certify non-reachability by exhibiting that many reachable configurations and showing the target is not among them.
-/
lemma NotReachable_Checkable {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) (N : ℕ) :
  ReachableCount M input n = N →
  ∀ c, ¬ ReachableInAtMost M (InitialConfig M input) c n ↔
  ∃ (S : Set (Configuration k σ M.V)),
    S.Finite ∧
    Nat.card S = N ∧
    (∀ s ∈ S, ReachableInAtMost M (InitialConfig M input) s n) ∧
    c ∉ S := by
  intro hN c
  rw [ReachableCount] at hN
  let P := fun x => ReachableInAtMost M (InitialConfig M input) x n
  let S_P := { x | P x }
  have hFinite : S_P.Finite := Finite_ReachableInAtMost M input n
  have hN' : Nat.card S_P = N := hN
  exact Set_Card_Certificate_Of_NonMembership P S_P rfl hFinite N hN' c

/-
This lemma justifies the inductive step in the counting argument. It shows that if we know the count of reachable configurations at step n, we can characterize the configurations reachable at step n+1 using a witness set S of that size. This characterization is what the NSPACE machine will verify.
-/
lemma Count_Next_Step {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) (N_prev : ℕ) :
  ReachableCount M input n = N_prev →
  ReachableCount M input (n + 1) =
  Nat.card { c | ∃ (S : Set (Configuration k σ M.V)),
    S.Finite ∧ Nat.card S = N_prev ∧
    (∀ s ∈ S, ReachableInAtMost M (InitialConfig M input) s n) ∧
    (c ∈ S ∨ ∃ s ∈ S, step M s c) } := by
      intro hN_prev;
      refine' Eq.symm ( Nat.card_congr _ );
      refine' Equiv.subtypeEquivRight _;
      intro c;
      constructor;
      · rintro ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩;
        exact hS₄.elim ( fun h => ReachableInAtMost_Mono _ _ _ n <| hS₃ _ h ) fun ⟨ s, hs₁, hs₂ ⟩ => ReachableInAtMost_Step _ _ _ _ n ( hS₃ _ hs₁ ) hs₂;
      · intro hc;
        use { s | ReachableInAtMost M (InitialConfig M input) s n };
        exact ⟨ Finite_ReachableInAtMost M input n, hN_prev ▸ rfl, fun s hs => hs, by cases ReachableInAtMost_Succ_Imp M input c n hc <;> tauto ⟩

/-
The number of reachable configurations is non-decreasing with the number of steps.
-/
lemma ReachableCount_Mono {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) :
  ReachableCount M input n ≤ ReachableCount M input (n + 1) := by
    apply_rules [ Nat.card_mono ];
    · exact?;
    · exact fun c hc => ReachableInAtMost_Mono M _ _ _ hc

/-
The number of reachable configurations is bounded by the total number of space-bounded configurations.
-/
lemma ReachableCount_Bounded {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) (n : ℕ) :
  ReachableCount M input n ≤ Nat.card { c : Configuration k σ M.V | BoundedConfig M (S input.length) input c } := by
    convert Nat.card_mono ?_ ?_ using 1;
    · convert FiniteBoundedConfig M ( S input.length ) input;
    · intro c hc;
      apply SpaceBounded_Implies_BoundedConfig M S hS input c;
      obtain ⟨ path, hpath₁, hpath₂, hpath₃, hpath₄ ⟩ := hc;
      have h_reachable : ∀ {l : List (Configuration k σ M.V)}, l ≠ [] → l.head? = some (InitialConfig M input) → l.getLast? = some c → List.Chain' (step M) l → Reachable M (InitialConfig M input) c := by
        intros l hl hl_head hl_last hl_chain
        induction' l with c l ih;
        · contradiction;
        · have h_reachable : ∀ {l : List (Configuration k σ M.V)}, l ≠ [] → List.Chain' (step M) l → ∀ {c c' : Configuration k σ M.V}, l.head? = some c → l.getLast? = some c' → Reachable M c c' := by
            intros l hl hl_chain c c' hl_head hl_last; induction' l with c l ih generalizing c c'; aesop;
            cases l <;> simp_all +decide [ List.isChain_cons_cons ];
            · constructor;
            · exact Relation.ReflTransGen.trans ( Relation.ReflTransGen.single ( by cases hl_chain ; tauto ) ) ( ih ( by cases hl_chain ; tauto ) rfl hl_last );
          exact h_reachable ( by aesop ) hl_chain ( by aesop ) hl_last;
      exact h_reachable ( by rintro rfl; contradiction ) hpath₂ hpath₃ hpath₄

/-
Check if Complement is defined.
-/
#check @Complement

/-
The complement of a language L is the set of strings not in L.
-/
def LanguageComplement {σ : Type} (L : Set (List σ)) : Set (List σ) :=
  { x | x ∉ L }

/-
Reflexive transitive closure is equivalent to existence of a chain.
-/
lemma ReflTransGen_iff_ListChain {α : Type} (R : α → α → Prop) (a b : α) :
  Relation.ReflTransGen R a b ↔ ∃ l : List α, l.Chain' R ∧ l.head? = some a ∧ l.getLast? = some b := by
    constructor <;> intro h;
    · have h_chain : ∀ {x y : α}, Relation.ReflTransGen R x y → ∃ l : List α, List.Chain' R l ∧ l.head? = some x ∧ l.getLast? = some y := by
        intro x y hxy;
        induction hxy;
        · exact ⟨ [ x ], List.isChain_singleton _, rfl, rfl ⟩;
        · rename_i l hl₁ hl₂ hl₃ hl₄;
          obtain ⟨ l, hl₅, hl₆, hl₇ ⟩ := hl₄; use l ++ [ hl₁ ] ; simp_all +decide [ List.Chain' ] ;
          simp_all +decide [ List.isChain_append ];
      exact h_chain h;
    · obtain ⟨ l, hl₁, hl₂, hl₃ ⟩ := h;
      induction' l with x l ih generalizing a b <;> simp_all +decide [ Relation.ReflTransGen ];
      rcases l <;> simp_all +decide [ List.chain'_cons' ];
      · exact Relation.ReflTransGen.refl;
      · exact Relation.ReflTransGen.trans ( Relation.ReflTransGen.single ( by cases hl₁ ; tauto ) ) ( ih _ _ ( by cases hl₁ ; tauto ) rfl hl₃ )

/-
If a chain has a duplicate, it can be shortened to a strictly shorter chain with the same endpoints.
-/
lemma Chain_shorten_of_duplicate {α : Type} (R : α → α → Prop) (l : List α)
  (h_chain : List.Chain' R l)
  (h_dup : ∃ i j : Fin l.length, i < j ∧ l.get i = l.get j) :
  ∃ l' : List α, List.Chain' R l' ∧ l'.head? = l.head? ∧ l'.getLast? = l.getLast? ∧ l'.length < l.length := by
    obtain ⟨i, j, hij, h_eq⟩ : ∃ i j, i < j ∧ l.get i = l.get j ∧ ∀ k, i < k → k < j → l.get i ≠ l.get k := by
      obtain ⟨i, j, hij, h_eq⟩ : ∃ i j, i < j ∧ l.get i = l.get j := h_dup;
      -- We'll use the fact that if there's a duplicate, we can find the smallest index $j$ such that $l.get i = l.get j$.
      obtain ⟨j, hj⟩ : ∃ j : Fin l.length, i < j ∧ l.get i = l.get j ∧ ∀ k : Fin l.length, i < k → k < j → l.get i ≠ l.get k := by
        have h_exists : ∃ j : Fin l.length, i < j ∧ l.get i = l.get j := by
          use j
        exact ⟨ Finset.min' ( Finset.univ.filter fun k => i < k ∧ l.get i = l.get k ) ⟨ j, by aesop ⟩, Finset.mem_filter.mp ( Finset.min'_mem ( Finset.univ.filter fun k => i < k ∧ l.get i = l.get k ) ⟨ j, by aesop ⟩ ) |>.2.1, Finset.mem_filter.mp ( Finset.min'_mem ( Finset.univ.filter fun k => i < k ∧ l.get i = l.get k ) ⟨ j, by aesop ⟩ ) |>.2.2, fun k hk₁ hk₂ hk₃ => not_lt_of_ge ( Finset.min'_le _ _ <| by aesop ) hk₂ ⟩;
      use i, j;
    refine' ⟨ l.take ( i + 1 ) ++ l.drop ( j + 1 ), _, _, _, _ ⟩;
    · refine' List.isChain_append.mpr ⟨ _, _, _ ⟩;
      · exact List.IsChain.take h_chain _;
      · have h_chain_drop : List.IsChain R (List.drop (j + 1) l) := by
          have h_chain_l : List.IsChain R l := by
            exact?
          exact h_chain_l.drop _;
        exact h_chain_drop;
      · have := List.isChain_iff_get.mp h_chain;
        rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +decide [ List.take_succ ];
        grind;
    · rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> aesop;
    · rw [ List.getLast?_append ];
      rw [ List.getLast?_drop ];
      rw [ List.getLast?_take ];
      grind;
    · grind

/-
If a chain is a shortest chain between its endpoints, it has no duplicates.
-/
lemma ShortestChain_is_Nodup {α : Type} (R : α → α → Prop) (l : List α)
  (h_chain : l.Chain' R)
  (h_min : ∀ l' : List α, l'.Chain' R → l'.head? = l.head? → l'.getLast? = l.getLast? → l.length ≤ l'.length) :
  l.Nodup := by
    contrapose! h_min;
    -- By definition of nodup, if l is not nodup, then there exist i < j such that l.get i = l.get j.
    obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : Fin l.length, i < j ∧ l.get i = l.get j := by
      rw [ List.nodup_iff_injective_get ] at h_min;
      obtain ⟨ i, j, hij, h ⟩ := Function.not_injective_iff.mp h_min; cases lt_trichotomy i j <;> aesop;
    obtain ⟨l', hl'⟩ : ∃ l' : List α, List.Chain' R l' ∧ l'.head? = l.head? ∧ l'.getLast? = l.getLast? ∧ l'.length < l.length := by
      have := Chain_shorten_of_duplicate R l h_chain ⟨i, j, hij, h_eq⟩
      exact this;
    use l'

/-
If there exists a chain from a to b, there exists a minimal length chain from a to b.
-/
lemma Exists_Minimal_Chain {α : Type} (R : α → α → Prop) (a b : α) :
  (∃ l : List α, l.Chain' R ∧ l.head? = some a ∧ l.getLast? = some b) →
  ∃ l : List α, l.Chain' R ∧ l.head? = some a ∧ l.getLast? = some b ∧
    ∀ l' : List α, l'.Chain' R → l'.head? = some a → l'.getLast? = some b → l.length ≤ l'.length := by
      intro h
      obtain ⟨l, hl⟩ := h
      generalize_proofs at *;
      have h_min : ∃ l : List α, List.Chain' R l ∧ l.head? = some a ∧ l.getLast? = some b ∧ ∀ l' : List α, List.Chain' R l' → l'.head? = some a → l'.getLast? = some b → l.length ≤ l'.length := by
        have h_exists : ∃ l : List α, List.Chain' R l ∧ l.head? = some a ∧ l.getLast? = some b := ⟨l, hl⟩
        obtain ⟨l, hl⟩ := h_exists
        have h_min : ∃ m : ℕ, m ∈ {n : ℕ | ∃ l : List α, List.Chain' R l ∧ l.head? = some a ∧ l.getLast? = some b ∧ l.length = n} ∧ ∀ n ∈ {n : ℕ | ∃ l : List α, List.Chain' R l ∧ l.head? = some a ∧ l.getLast? = some b ∧ l.length = n}, m ≤ n := by
          exact ⟨ Nat.find ⟨ _, ⟨ l, hl.1, hl.2.1, hl.2.2, rfl ⟩ ⟩, Nat.find_spec ( ⟨ _, ⟨ l, hl.1, hl.2.1, hl.2.2, rfl ⟩ ⟩ : ∃ n, ∃ l : List α, List.Chain' R l ∧ l.head? = some a ∧ l.getLast? = some b ∧ l.length = n ), fun n hn => Nat.find_min' _ hn ⟩
        obtain ⟨ m, ⟨ l, hl₁, hl₂, hl₃, rfl ⟩, hm ⟩ := h_min; exact ⟨ l, hl₁, hl₂, hl₃, fun l' hl₁' hl₂' hl₃' => hm _ ⟨ l', hl₁', hl₂', hl₃', rfl ⟩ ⟩ ;
      generalize_proofs at *; (
      exact h_min)

/-
If there is a chain, there is a simple chain.
-/
lemma ListChain_imp_NodupListChain {α : Type} [DecidableEq α] (R : α → α → Prop) (a b : α) :
  (∃ l : List α, l.Chain' R ∧ l.head? = some a ∧ l.getLast? = some b) →
  ∃ l : List α, l.Chain' R ∧ l.head? = some a ∧ l.getLast? = some b ∧ l.Nodup := by
    intro h
    obtain ⟨l, hl_chain, hl_head, hl_last⟩ := h
    obtain ⟨l', hl'_chain, hl'_head, hl'_last, hl'_min⟩ : ∃ l' : List α, l'.Chain' R ∧ l'.head? = some a ∧ l'.getLast? = some b ∧
      ∀ l'' : List α, l''.Chain' R → l''.head? = some a → l''.getLast? = some b → l'.length ≤ l''.length := by
        exact Exists_Minimal_Chain R a b ⟨ l, hl_chain, hl_head, hl_last ⟩ |> fun ⟨ l', hl'_chain, hl'_head, hl'_last, hl'_min ⟩ => ⟨ l', hl'_chain, hl'_head, hl'_last, fun l'' hl''_chain hl''_head hl''_last => hl'_min l'' hl''_chain hl''_head hl''_last ⟩;
    refine' ⟨ l', hl'_chain, hl'_head, hl'_last, _ ⟩;
    apply_rules [ ShortestChain_is_Nodup ];
    grind

/-
If `l` is a chain starting at `a`, then every element in `l` is reachable from `a`.
-/
lemma Chain_implies_Reachable {α : Type} (R : α → α → Prop) (l : List α) (a : α) :
  l.Chain' R → l.head? = some a → ∀ x ∈ l, Relation.ReflTransGen R a x := by
    intro hL ha x hxop;
    induction' l with y l ih generalizing a x;
    · contradiction;
    · cases l <;> simp_all +decide [ Relation.ReflTransGen.refl, Relation.ReflTransGen.single ];
      rcases hxop with ( rfl | rfl | hxop ) <;> [ tauto; exact Relation.ReflTransGen.single ( by cases hL ; tauto ) ; exact Relation.ReflTransGen.trans ( Relation.ReflTransGen.single ( by cases hL ; tauto ) ) ( ih ( by cases hL ; tauto ) _ hxop ) ]

/-
The length of a Nodup list of elements satisfying P is at most the cardinality of {x | P x}.
-/
lemma Nodup_List_Length_Le_Card {α : Type} (P : α → Prop) [DecidablePred P] (l : List α)
  (h_nodup : l.Nodup) (h_subset : ∀ x ∈ l, P x) (h_finite : Set.Finite {x | P x}) :
  l.length ≤ Nat.card {x | P x} := by
    have h_card : l.toFinset.card ≤ Nat.card {x | P x} := by
      rw [ ← Nat.card_eq_finsetCard ];
      apply_rules [ Nat.card_mono ];
      exact fun x hx => h_subset x <| List.mem_toFinset.mp hx;
    rwa [ List.toFinset_card_of_nodup h_nodup ] at h_card

/-
Reachable iff ReachableInAtMost Max.
-/
lemma Reachable_iff_ReachableInAtMost_Max {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) (c : Configuration k σ M.V) :
  Reachable M (InitialConfig M input) c ↔
  ReachableInAtMost M (InitialConfig M input) c (Nat.card { x | BoundedConfig M (S input.length) input x }) := by
    constructor;
    · intro hc
      obtain ⟨l, hl_chain, hl_head, hl_last⟩ : ∃ l : List (Configuration k σ M.V), l.Chain' (step M) ∧ l.head? = some (InitialConfig M input) ∧ l.getLast? = some c := by
        exact?;
      -- By Lemma `ListChain_imp_NodupListChain`, there exists a Nodup chain `l'` from `InitialConfig M input` to `c`.
      obtain ⟨l', hl'_chain, hl'_head, hl'_last, hl'_nodup⟩ : ∃ l' : List (Configuration k σ M.V), l'.Chain' (step M) ∧ l'.head? = some (InitialConfig M input) ∧ l'.getLast? = some c ∧ l'.Nodup := by
        apply ListChain_imp_NodupListChain;
        use l;
      -- By Lemma `Nodup_List_Length_Le_Card`, the length of `l'` is at most the cardinality of the set of BoundedConfigs.
      have hl'_length : l'.length ≤ Nat.card {x : Configuration k σ M.V | BoundedConfig M (S input.length) input x} := by
        apply_rules [ Nodup_List_Length_Le_Card ];
        · intro x hx
          have hx_reachable : Reachable M (InitialConfig M input) x := by
            have hx_reachable : ∀ x ∈ l', Reachable M (InitialConfig M input) x := by
              apply_rules [ Chain_implies_Reachable ];
            exact hx_reachable x hx
          exact SpaceBounded_Implies_BoundedConfig M S hS input x hx_reachable;
        · exact?;
      use l';
      exact ⟨ Nat.le_succ_of_le hl'_length, hl'_head, hl'_last, hl'_chain ⟩;
    · intro h_reachable_in_at_most
      obtain ⟨path, hpath_length, hpath_head, hpath_last, hpath_chain⟩ := h_reachable_in_at_most;
      convert ReflTransGen_iff_ListChain _ _ _ |>.2 ⟨ path, hpath_chain, hpath_head, hpath_last ⟩

/-
The number of bounded configurations is at most the size of the configuration space.
-/
def ConfigSpaceSize {k : ℕ} {σ : Type} [Fintype σ] (M : TuringMachine k σ) (S : ℕ) : ℕ :=
  (@Fintype.card M.V M.fintypeV) * ((2 * S + 1) ^ k) * ((Fintype.card σ) ^ ((k - 1) * (S + 1)))

lemma Card_BoundedConfig_Le_ConfigSpaceSize {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ) (input : List σ) :
  Nat.card { c | BoundedConfig M S input c } ≤ ConfigSpaceSize M S := by
    by_contra h_contra;
    -- Let's construct the injection from the set of bounded configurations to the configuration space.
    have h_inj : {c : Configuration k σ M.V | BoundedConfig M S input c} ↪ M.V × (Fin k → Fin (2 * S + 1)) × (Fin (k - 1) → Fin (S + 1) → σ) := by
      refine' ⟨ _, _ ⟩;
      refine' fun c => ⟨ c.val.state, fun i => ⟨ Int.toNat ( c.val.positions i + S ), _ ⟩, fun i => fun n => c.val.tapes ⟨ i.val + 1, _ ⟩ n ⟩;
      all_goals norm_num [ Function.Injective ];
      all_goals norm_num [ funext_iff ];
      any_goals linarith [ Fin.is_lt i, Nat.sub_add_cancel ( NeZero.pos k ) ];
      · linarith [ abs_le.mp ( show |( c.val.positions i : ℤ )| ≤ S from by simpa [ ← Int.ofNat_le ] using c.2.1 i ) ];
      · intro a ha b hb hab hpos htape;
        -- Since the positions and tapes are equal, the configurations must be equal.
        have h_eq : a.positions = b.positions ∧ a.tapes = b.tapes := by
          have h_eq : a.positions = b.positions := by
            ext i;
            have := hpos i;
            linarith [ Int.toNat_of_nonneg ( show 0 ≤ a.positions i + S by linarith [ abs_le.mp ( show |a.positions i| ≤ S by linarith [ ha.1 i ] ) ] ), Int.toNat_of_nonneg ( show 0 ≤ b.positions i + S by linarith [ abs_le.mp ( show |b.positions i| ≤ S by linarith [ hb.1 i ] ) ] ) ];
          refine' ⟨ h_eq, funext fun i => funext fun n => _ ⟩;
          by_cases hi : i.val = 0;
          · have := ha.2.1 n; have := hb.2.1 n; aesop;
          · by_cases hn : n ≤ S;
            · convert htape ⟨ i.val - 1, _ ⟩ ⟨ n, _ ⟩ using 1;
              all_goals norm_num [ Nat.lt_succ_iff, Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr hi ) ];
              · exact tsub_lt_tsub_iff_right ( Nat.one_le_iff_ne_zero.mpr hi ) |>.2 i.2;
              · exact?;
            · have := ha.2.2 i; have := hb.2.2 i; aesop;
        cases a ; cases b ; aesop;
    convert Nat.card_le_card_of_injective h_inj h_inj.injective using 1;
    · simp +decide [ ConfigSpaceSize ];
      convert h_contra using 1;
      rw [ mul_left_comm, ← pow_mul ];
      simp +decide [ mul_comm, mul_assoc, mul_left_comm, ConfigSpaceSize ];
      congr!;
      convert Nat.card_eq_fintype_card;
    · haveI := M.fintypeV; infer_instance;

/-
A configuration is reachable iff it is reachable within `MaxSteps`.
-/
def MaxSteps {k : ℕ} {σ : Type} [Fintype σ] (M : TuringMachine k σ) (S : ℕ) : ℕ :=
  ConfigSpaceSize M S

lemma Reachable_iff_ReachableInAtMost_MaxSteps {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) (c : Configuration k σ M.V) :
  Reachable M (InitialConfig M input) c ↔
  ReachableInAtMost M (InitialConfig M input) c (MaxSteps M (S input.length)) := by
    constructor;
    · intro hc
      have h_card : ReachableInAtMost M (InitialConfig M input) c (Nat.card { x | BoundedConfig M (S input.length) input x }) := by
        exact?;
      have h_card_le : Nat.card { x | BoundedConfig M (S input.length) input x } ≤ ConfigSpaceSize M (S input.length) := by
        convert Card_BoundedConfig_Le_ConfigSpaceSize M ( S input.length ) input using 1;
      have h_card_le : ∀ n m : ℕ, n ≤ m → ReachableInAtMost M (InitialConfig M input) c n → ReachableInAtMost M (InitialConfig M input) c m := by
        intros n m hnm h_reachable_n
        induction' hnm with m ih;
        · assumption;
        · exact?;
      exact h_card_le _ _ ( by unfold MaxSteps; aesop ) h_card;
    · -- By definition of ReachableInAtMost, if c is reachable in at most MaxSteps steps, then there exists a path of configurations from the initial configuration to c with length at most MaxSteps.
      intro h_reachable
      obtain ⟨path, hpath_length, hpath_head, hpath_last, hpath_chain⟩ := h_reachable;
      convert ReflTransGen_iff_ListChain _ _ _ |>.2 ⟨ path, hpath_chain, hpath_head, hpath_last ⟩

/-
The condition that M does not accept input is equivalent to the existence of a count N and a set S of size N of reachable non-accepting configurations.
-/
lemma Immerman_Condition_Equivalence {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) :
  (¬ AcceptsN M input) ↔
  ∃ (N : ℕ), ReachableCount M input (MaxSteps M (S input.length)) = N ∧
  ∃ (S_set : Set (Configuration k σ M.V)),
    S_set ⊆ { c | Reachable M (InitialConfig M input) c } ∧
    Nat.card S_set = N ∧
    ∀ c ∈ S_set, c.state ≠ M.acceptState := by
      constructor;
      · intro h_not_accept;
        -- Let `S_set` be the set of all reachable configurations.
        set S_set := {c : Configuration k σ M.V | Reachable M (InitialConfig M input) c};
        refine' ⟨ _, rfl, S_set, Set.Subset.refl _, _, _ ⟩;
        · -- By definition of $S_set$, we know that every element in $S_set$ is reachable in at most $MaxSteps$ steps.
          have hS_set_subset : S_set = {c : Configuration k σ M.V | ReachableInAtMost M (InitialConfig M input) c (MaxSteps M (S input.length))} := by
            exact Set.ext fun x => Reachable_iff_ReachableInAtMost_MaxSteps M S hS input x;
          exact hS_set_subset ▸ rfl;
        · exact fun c hc => fun h => h_not_accept ⟨ c, hc, h ⟩;
      · rintro ⟨ N, rfl, S_set, hS_set₁, hS_set₂, hS_set₃ ⟩ h;
        obtain ⟨ c, hc₁, hc₂ ⟩ := h;
        -- Since $S_set$ is a subset of the reachable configurations and has the same cardinality, it must be equal to the set of all reachable configurations.
        have hS_set_eq : S_set = {c | Reachable M (InitialConfig M input) c} := by
          apply Set.eq_of_subset_of_ncard_le;
          · assumption;
          · rw [ show { c | Reachable M ( InitialConfig M input ) c } = { c | ReachableInAtMost M ( InitialConfig M input ) c ( MaxSteps M ( S input.length ) ) } from ?_ ];
            · unfold ReachableCount at hS_set₂; aesop;
            · exact Set.ext fun x => Reachable_iff_ReachableInAtMost_MaxSteps M S hS input x;
          · exact Set.Finite.subset ( FiniteBoundedConfig M ( S input.length ) input ) fun c hc => SpaceBounded_Implies_BoundedConfig M S hS input c hc;
        exact hS_set₃ c ( hS_set_eq ▸ hc₁ ) hc₂

/-
A sequence of numbers Ns is a valid count sequence if it starts with 1 and each subsequent number is the count of configurations reachable in the next step, computed using the previous count.
-/
def ValidCountSequence {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (Ns : List ℕ) : Prop :=
  Ns ≠ [] ∧
  Ns.head! = 1 ∧
  ∀ i : Fin (Ns.length - 1),
    let n := i.val
    let N_prev := Ns.get! n
    let N_curr := Ns.get! (n + 1)
    N_curr = Nat.card { c | ∃ (S : Set (Configuration k σ M.V)),
      S.Finite ∧ Nat.card S = N_prev ∧
      (∀ s ∈ S, ReachableInAtMost M (InitialConfig M input) s n) ∧
      (c ∈ S ∨ ∃ s ∈ S, step M s c) }

/-
If Ns is a valid count sequence, then the i-th element of Ns is the number of configurations reachable in at most i steps.
-/
lemma ValidCountSequence_Correct {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (Ns : List ℕ) :
  ValidCountSequence M input Ns →
  ∀ i : Fin Ns.length, Ns.get i = ReachableCount M input i := by
    intro h i;
    induction' i with i ih;
    induction' i with i ih;
    · convert h.2.1;
      · cases Ns <;> trivial;
      · exact?;
    · have := h.2.2 ⟨ i, by omega ⟩;
      convert this using 1;
      · exact Eq.symm ( by aesop );
      · convert Count_Next_Step M input i _ using 1;
        swap;
        exact Ns.get! i;
        simp +zetaDelta at *;
        exact Or.inl ( by rw [ List.getElem?_eq_getElem ( by linarith ) ] ; exact Eq.symm ( by solve_by_elim [ Nat.lt_of_succ_lt ] ) )

/-
A Turing machine M rejects an input iff there exists an Immerman witness (a sequence of counts and a set of final configurations) certifying non-acceptance.
-/
def ImmermanWitness {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) (Ns : List ℕ) (S_final : Set (Configuration k σ M.V)) : Prop :=
  ValidCountSequence M input Ns ∧
  Ns.length = MaxSteps M (S input.length) + 1 ∧
  Nat.card S_final = Ns.getLast! ∧
  (∀ c ∈ S_final, ReachableInAtMost M (InitialConfig M input) c (MaxSteps M (S input.length))) ∧
  (∀ c ∈ S_final, c.state ≠ M.acceptState)

theorem ImmermanWitness_Correct {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) :
  (¬ AcceptsN M input) ↔ ∃ Ns S_final, ImmermanWitness M S hS input Ns S_final := by
    constructor;
    · intro h_not_accept
      obtain ⟨N, hN⟩ := Immerman_Condition_Equivalence M S hS input |>.1 h_not_accept;
      obtain ⟨S_final, hS_final⟩ := hN.2;
      use List.map (fun i => ReachableCount M input i) (List.range (MaxSteps M (S input.length) + 1)), S_final;
      constructor;
      · constructor;
        · simp +decide [ List.range_succ_eq_map ];
        · constructor;
          · simp +decide [ List.range_succ_eq_map, ReachableCount_Zero ];
          · intro i
            simp [List.get!];
            rw [ List.getElem?_range, List.getElem?_range ] <;> norm_num;
            · convert Count_Next_Step M input i ( ReachableCount M input i ) rfl using 1;
            · exact Nat.lt_succ_of_lt ( Nat.lt_of_lt_of_le i.2 ( by simp +arith +decide ) );
            · exact Nat.lt_of_lt_of_le i.2 ( by simp +arith +decide );
      · simp_all +decide [ List.range_succ ];
        exact fun c hc => Reachable_iff_ReachableInAtMost_MaxSteps M S hS input c |>.1 ( hS_final.1 hc );
    · rintro ⟨ Ns, S_final, hNs, hS_final ⟩;
      -- By definition of `ValidCountSequence`, we know that `Ns.getLast! = ReachableCount M input (MaxSteps M (S input.length))`.
      have h_last : Ns.getLast! = ReachableCount M input (MaxSteps M (S input.length)) := by
        convert ValidCountSequence_Correct M input Ns hNs ⟨ MaxSteps M ( S input.length ), by linarith ⟩ using 1;
        grind;
      have h_card : ∀ c, Reachable M (InitialConfig M input) c → c ∈ { c | ReachableInAtMost M (InitialConfig M input) c (MaxSteps M (S input.length)) } := by
        exact fun c hc => Reachable_iff_ReachableInAtMost_MaxSteps M S hS input c |>.1 hc;
      have h_card : S_final = { c | ReachableInAtMost M (InitialConfig M input) c (MaxSteps M (S input.length)) } := by
        apply Set.eq_of_subset_of_ncard_le;
        · exact fun x hx => hS_final.2.2.1 x hx;
        · aesop;
        · exact?;
      simp_all +decide [ AcceptsN ]

/-
The integer logarithm of a product is at most the sum of the logarithms plus one.
-/
lemma Nat.log2_mul_le (a b : ℕ) : Nat.log2 (a * b) ≤ Nat.log2 a + Nat.log2 b + 1 := by
  rcases a with ( _ | a ) <;> rcases b with ( _ | b ) <;> simp_all +decide [ Nat.log2 ];
  -- By definition of logarithm, we know that if $a > 0$ and $b > 0$, then $2^{\log_2 a} \le a < 2^{\log_2 a + 1}$ and $2^{\log_2 b} \le b < 2^{\log_2 b + 1}$.
  have h_log_bounds : 2 ^ Nat.log2 (a + 1) ≤ a + 1 ∧ a + 1 < 2 ^ (Nat.log2 (a + 1) + 1) ∧ 2 ^ Nat.log2 (b + 1) ≤ b + 1 ∧ b + 1 < 2 ^ (Nat.log2 (b + 1) + 1) := by
    rw [ ← Nat.le_log2, ← Nat.log2_lt ] <;> norm_num;
    rw [ ← Nat.le_log2, ← Nat.log2_lt ] <;> norm_num;
  -- Therefore, $2^{\log_2 (a + 1) + \log_2 (b + 1)} \le (a + 1)(b + 1) < 2^{\log_2 (a + 1) + \log_2 (b + 1) + 2}$.
  have h_prod_bounds : 2 ^ (Nat.log2 (a + 1) + Nat.log2 (b + 1)) ≤ (a + 1) * (b + 1) ∧ (a + 1) * (b + 1) < 2 ^ (Nat.log2 (a + 1) + Nat.log2 (b + 1) + 2) := by
    exact ⟨ by simpa only [ pow_add ] using Nat.mul_le_mul h_log_bounds.1 h_log_bounds.2.2.1, by convert Nat.mul_lt_mul'' h_log_bounds.2.1 h_log_bounds.2.2.2 using 1 ; ring ⟩;
  -- Therefore, $\log_2((a + 1)(b + 1)) \leq \log_2(a + 1) + \log_2(b + 1) + 1$.
  have h_log_prod : Nat.log2 ((a + 1) * (b + 1)) ≤ Nat.log2 (a + 1) + Nat.log2 (b + 1) + 1 := by
    rw [ Nat.le_iff_lt_or_eq ];
    refine' lt_or_eq_of_le ( Nat.le_of_lt_succ _ );
    rw [ Nat.log2_lt ] <;> norm_num ; linarith;
  convert h_log_prod using 1

/-
The integer logarithm of a power is at most the exponent times the logarithm of the base plus one.
-/
lemma Nat.log2_pow_le (a b : ℕ) : Nat.log2 (a ^ b) ≤ b * (Nat.log2 a + 1) := by
  -- Apply the lemma Nat.log2_mul_le to Powers.
  have h_log2_mul : ∀ a b : ℕ, Nat.log2 (a ^ b) ≤ b * (Nat.log2 a + 1) := by
    intro a b; induction' b with b ih <;> simp_all +decide [ Nat.mul_succ, pow_succ' ] ;
    -- Apply the lemma Nat.log2_mul_le to a and a^b.
    have h_log2_mul_le : Nat.log2 (a * a ^ b) ≤ Nat.log2 a + Nat.log2 (a ^ b) + 1 := by
      exact?;
    linarith;
  exact h_log2_mul a b

/-
The number of bits required to represent MaxSteps is bounded by a linear function of S.
-/
lemma Log_MaxSteps_Bound {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ) (hS : S > 0) :
  Nat.log2 (MaxSteps M S) ≤ Nat.log2 (@Fintype.card M.V M.fintypeV) + k * (Nat.log2 (2 * S + 1) + 1) + (k - 1) * (S + 1) * (Nat.log2 (Fintype.card σ) + 1) + 2 := by
    -- Apply the lemma Nat.log2_mul_le to each multiplication step.
    have h_log2_mul : ∀ a b : ℕ, Nat.log2 (a * b) ≤ Nat.log2 a + Nat.log2 b + 1 := by
      exact?;
    refine le_trans ( h_log2_mul _ _ ) ?_;
    -- Apply the lemma Nat.log2_pow_le to each term.
    have h_log2_pow : ∀ a b : ℕ, Nat.log2 (a ^ b) ≤ b * (Nat.log2 a + 1) := by
      exact?;
    grind

/-
The integer logarithm of a product of three numbers is at most the sum of their logarithms plus two.
-/
lemma Nat.log2_mul3_le (a b c : ℕ) : Nat.log2 (a * b * c) ≤ Nat.log2 a + Nat.log2 b + Nat.log2 c + 2 := by
  have h_log : Nat.log2 (a * b * c) ≤ Nat.log2 a + Nat.log2 b + Nat.log2 c + 2 := by
    have h_log_mul : ∀ a b : ℕ, Nat.log2 (a * b) ≤ Nat.log2 a + Nat.log2 b + 1 := by
      exact?
    grind;
  exact?

#check Log_MaxSteps_Bound

/-
Assuming the Immerman construction exists, NSPACE is closed under complementation.
-/
def Immerman_Construction_Exists_Prop : Prop :=
  ∀ {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (hS_log : ∀ n, S n ≥ Nat.log2 n),
  ∃ (k' : ℕ) (hk' : NeZero k') (M' : TuringMachine k' σ),
    @SpaceBounded k' σ _ hk' M' (fun n => 10 * S n) ∧
    ∀ x, AcceptsN M' x ↔ ¬ AcceptsN M x

theorem NSPACE_Closed_Under_Complement_Conditional
  (h_construct : Immerman_Construction_Exists_Prop)
  {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (S : ℕ → ℕ) (hS : ∀ n, S n ≥ Nat.log2 n) (L : Set (List σ)) :
  InNSPACE S L → InNSPACE (fun n => 10 * S n) (LanguageComplement L) := by
    intro hL;
    rcases hL with ⟨ k, hk, M, hM, hM' ⟩;
    convert h_construct _;
    any_goals assumption;
    constructor <;> intro h;
    · exact?;
    · obtain ⟨ k', hk', M', hM', hM'' ⟩ := h S hM hS;
      use k', hk', M';
      unfold LanguageRecognizedByN LanguageComplement; aesop;

theorem ImmermanWitness_Correct_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) :
  (¬ AcceptsN M input) ↔ ∃ Ns S_final, ImmermanWitness M S hS input Ns S_final := by
    have := @ImmermanWitness_Correct;
    exact this M S hS input

/-
If the Immerman construction exists, then NSPACE is closed under complementation (with a linear space blowup).
-/
theorem NSPACE_Closed_Under_Complement_Conditional_Proof
  (h_construct : Immerman_Construction_Exists_Prop)
  {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (S : ℕ → ℕ) (hS : ∀ n, S n ≥ Nat.log2 n) (L : Set (List σ)) :
  InNSPACE S L → InNSPACE (fun n => 10 * S n) (LanguageComplement L) := by
    exact?

/-
If the count of configurations reachable in n steps is N_prev, then the count of configurations reachable in n+1 steps is the size of the set of configurations c such that there exists a witness set S of size N_prev of reachable-in-n configurations, where c is either in S or a successor of S.
-/
theorem Count_Next_Step_Thm {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) (N_prev : ℕ) :
  ReachableCount M input n = N_prev →
  ReachableCount M input (n + 1) =
  Nat.card { c | ∃ (S : Set (Configuration k σ M.V)),
    S.Finite ∧ Nat.card S = N_prev ∧
    (∀ s ∈ S, ReachableInAtMost M (InitialConfig M input) s n) ∧
    (c ∈ S ∨ ∃ s ∈ S, step M s c) } := by
      exact?

/-
If Ns is a valid count sequence, then the i-th element of Ns is the number of configurations reachable in at most i steps.
-/
theorem ValidCountSequence_Correct_Proved {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (Ns : List ℕ) :
  ValidCountSequence M input Ns →
  ∀ i : Fin Ns.length, Ns.get i = ReachableCount M input i := by
    -- Apply the lemma ValidCountSequence_Correct to conclude the proof.
    apply ValidCountSequence_Correct

/-
A Turing machine M rejects an input if and only if there exists an Immerman witness (a sequence of counts and a set of final configurations) certifying non-acceptance.
-/
theorem ImmermanWitness_Theorem {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) :
  (¬ AcceptsN M input) ↔ ∃ Ns S_final, ImmermanWitness M S hS input Ns S_final := by
    convert ImmermanWitness_Correct M S hS input using 1

/-
The set of tapes with content bounded by S (i.e., default value for indices > S) is finite.
-/
lemma FiniteBoundedTape_Proof {σ : Type} [Fintype σ] [Inhabited σ] [DecidableEq σ] (S : ℕ) :
  Set.Finite { t : ℕ → σ | ∀ n, n > S → t n = default } := by
    exact FiniteBoundedTape S |> Set.Finite.subset <| fun t ht => ht

/-
The set of bounded tapes (tape 0 fixed, others bounded by S) is finite.
-/
lemma FiniteBoundedTapes_Proof (k : ℕ) (σ : Type) [Fintype σ] [Inhabited σ] [DecidableEq σ] [NeZero k] (S : ℕ) (input : List σ) :
  Set.Finite { ts | BoundedTapes k σ S input ts } := by
    convert FiniteBoundedTapes k σ S input using 1

/-
The set of bounded positions (each coordinate in [-S, S]) is finite.
-/
lemma FiniteBoundedPositions_Proof (k : ℕ) (S : ℕ) :
  Set.Finite { ps : Fin k → ℤ | BoundedPositions k S ps } := by
    have h_finite_positions : Set.Finite {ps : Fin k → ℤ | ∀ i, |ps i| ≤ S} := by
      have : ∀ i : Fin k, Set.Finite {x : ℤ | |x| ≤ S} := by
        exact fun i => Set.Finite.subset ( Set.finite_Icc ( - ( S : ℤ ) ) ( S : ℤ ) ) fun x hx => ⟨ neg_le_of_abs_le hx, le_of_abs_le hx ⟩
      exact Set.Finite.subset ( Set.Finite.pi fun i => this i ) fun x hx => by aesop;;
    exact h_finite_positions.subset fun x hx => fun i => by simpa [ ← Int.ofNat_le ] using hx i;

/-
The set of bounded configuration tuples (state, tapes, positions) is finite.
-/
lemma FiniteBoundedConfigTuples_Proof {k : ℕ} [NeZero k] (M : TuringMachine k σ) (S : ℕ) (input : List σ) :
  Set.Finite (BoundedConfigTuples M S input) := by
    exact?

/-
The set of states is finite.
-/
lemma FiniteStates_Proof {k : ℕ} (M : TuringMachine k σ) : Set.Finite (Set.univ : Set M.V) := by
  convert Set.finite_univ;
  convert M.fintypeV.finite

/-
If a Turing machine is space-bounded by S, then every reachable configuration is a BoundedConfig (positions within S, tapes default outside S).
-/
lemma SpaceBounded_Implies_BoundedConfig_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hM : SpaceBounded M S) (input : List σ) (c : Configuration k σ M.V) :
  Reachable M (InitialConfig M input) c → BoundedConfig M (S input.length) input c := by
    -- By definition of Reachable, we need to consider three cases: when c is the initial configuration, when c is obtained by a step from some reachable configuration c', and when c is obtained by transitive closure of reachability.
    apply SpaceBounded_Implies_BoundedConfig M S hM input c

/-
If the Immerman construction exists, then NSPACE is closed under complementation.
-/
theorem NSPACE_Closed_Under_Complement_Conditional_Thm
  (h_construct : Immerman_Construction_Exists_Prop)
  {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (S : ℕ → ℕ) (hS : ∀ n, S n ≥ Nat.log2 n) (L : Set (List σ)) :
  InNSPACE S L → InNSPACE (fun n => 10 * S n) (LanguageComplement L) := by
    -- Apply the Immerman construction hypothesis to obtain the existence of the required Turing machine.
    apply NSPACE_Closed_Under_Complement_Conditional h_construct S hS L

/-
The number of bits required to represent MaxSteps is bounded by a linear function of S.
-/
lemma Log_MaxSteps_Bound_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ) (hS : S > 0) :
  Nat.log2 (MaxSteps M S) ≤ Nat.log2 (@Fintype.card M.V M.fintypeV) + k * (Nat.log2 (2 * S + 1) + 1) + (k - 1) * (S + 1) * (Nat.log2 (Fintype.card σ) + 1) + 2 := by
    convert Log_MaxSteps_Bound M S hS using 1

/-
The integer logarithm of a product of three numbers is at most the sum of their logarithms plus two.
-/
lemma Nat.log2_mul3_le_Proof (a b c : ℕ) : Nat.log2 (a * b * c) ≤ Nat.log2 a + Nat.log2 b + Nat.log2 c + 2 := by
  exact?

/-
The integer logarithm of a power is at most the exponent times the logarithm of the base plus one.
-/
lemma Nat.log2_pow_le_Proof (a b : ℕ) : Nat.log2 (a ^ b) ≤ b * (Nat.log2 a + 1) := by
  exact?

/-
The set of configurations reachable in at most n steps is finite.
-/
lemma FiniteReachableSet_Proof {k : ℕ} [NeZero k] (M : TuringMachine k σ) (input : List σ) (n : ℕ) :
  Set.Finite (ReachableSet M input n) := by
    exact?

/-
The set of edges in the Turing machine is finite.
-/
lemma FiniteEdges_Proof {k : ℕ} [NeZero k] (M : TuringMachine k σ) : Set.Finite M.edges := by
  have h_finite_edges : Finite (M.V × M.V × (Fin k → σ) × (Fin (k-1) → σ) × (Fin k → Move)) := by
    haveI := M.fintypeV; infer_instance;
  exact Set.toFinite _

/-
If a configuration is reachable in at most n steps, it is reachable in at most n+1 steps.
-/
lemma ReachableInAtMost_Mono_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (c1 c2 : Configuration k σ M.V) (n : ℕ) :
  ReachableInAtMost M c1 c2 n → ReachableInAtMost M c1 c2 (n + 1) := by
    exact?

/-
The number of reachable configurations is non-decreasing with the number of steps.
-/
lemma ReachableCount_Mono_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) :
  ReachableCount M input n ≤ ReachableCount M input (n + 1) := by
    exact?

/-
If a configuration is reachable in at most n+1 steps, it is either reachable in at most n steps or it is a successor of a configuration reachable in at most n steps.
-/
lemma ReachableInAtMost_Succ_Imp_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) (c' : Configuration k σ M.V) (n : ℕ) :
  ReachableInAtMost M (InitialConfig M input) c' (n + 1) →
  ReachableInAtMost M (InitialConfig M input) c' n ∨
  ∃ c, ReachableInAtMost M (InitialConfig M input) c n ∧ step M c c' := by
    convert ReachableInAtMost_Succ_Imp M input c' n using 1

/-
The number of reachable configurations is bounded by the total number of space-bounded configurations.
-/
lemma ReachableCount_Bounded_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) (n : ℕ) :
  ReachableCount M input n ≤ Nat.card { c : Configuration k σ M.V | BoundedConfig M (S input.length) input c } := by
    apply le_trans (ReachableCount_Mono M input n) (ReachableCount_Bounded M S hS input (n + 1))

/-
The set of configurations reachable in 0 steps is exactly the singleton set containing the initial configuration.
-/
lemma ReachableInAtMost_Zero_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) :
  { c | ReachableInAtMost M (InitialConfig M input) c 0 } = { InitialConfig M input } := by
    convert ReachableInAtMost_Zero M input using 1

/-
If c' is a valid successor of c, then c' is in the set of potential next configurations.
-/
lemma Step_implies_NextConfigs {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (c c' : Configuration k σ M.V) :
  step M c c' → c' ∈ NextConfigs M c := by
    intro h
    obtain ⟨r, w, m, he, hc'⟩ := h;
    unfold NextConfigs;
    unfold EdgeToNextConfig;
    refine' ⟨ _, he, _ ⟩ ; simp +decide [ NextConfig ];
    congr with i n ; rcases i with ⟨ _ | i, hi ⟩ <;> simp_all +decide [ Fin.ext_iff ];
    · grind;
    · rw [ hc'.2.2.2.1 ]

/-
If c is reachable in at most n steps and c -> c', then c' is reachable in at most n+1 steps.
-/
lemma ReachableInAtMost_Step_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) (c c' : Configuration k σ M.V) (n : ℕ) :
  ReachableInAtMost M (InitialConfig M input) c n → step M c c' →
  ReachableInAtMost M (InitialConfig M input) c' (n + 1) := by
    exact?

/-
The set of configurations reachable in at most n steps is a subset of the recursively defined ReachableSet.
-/
lemma ReachableInAtMost_subset_ReachableSet {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) :
  { c | ReachableInAtMost M (InitialConfig M input) c n } ⊆ ReachableSet M input n := by
    intro c hc
    induction' n with n ih generalizing c
    · -- Base case: n = 0
      exact (by
      exact Set.mem_singleton_iff.mp ( ReachableInAtMost_Zero M input ▸ hc ) ▸ rfl)
    · -- Inductive step: Assume the statement holds for n, show it for n + 1
      exact (by
      by_cases hc' : c ∈ { c | ReachableInAtMost M (InitialConfig M input) c n };
      · exact Set.mem_union_left _ ( ih hc' );
      · -- By definition of ReachableInAtMost, there exists some c' such that c' is reachable in n steps and there's a step from c' to c.
        obtain ⟨c', hc', h_step⟩ : ∃ c', ReachableInAtMost M (InitialConfig M input) c' n ∧ step M c' c := by
          exact ReachableInAtMost_Succ_Imp M input c n hc |> fun h => h.resolve_left hc' |> fun ⟨ c', hc', h_step ⟩ => ⟨ c', hc', h_step ⟩;
        exact Set.mem_union_right _ ( Set.mem_sUnion.mpr ⟨ _, Set.mem_image_of_mem _ ( ih hc' ), Step_implies_NextConfigs M c' c h_step ⟩ ))
    skip

/-
The set of configurations reachable in at most n steps is a subset of the recursively defined ReachableSet.
-/
lemma ReachableInAtMost_subset_ReachableSet_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) :
  { c | ReachableInAtMost M (InitialConfig M input) c n } ⊆ ReachableSet M input n := by
    apply ReachableInAtMost_subset_ReachableSet M input n

/-
The set of configurations reachable in at most n steps is finite.
-/
lemma Finite_ReachableInAtMost_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) :
  Set.Finite { c | ReachableInAtMost M (InitialConfig M input) c n } := by
    exact FiniteReachableSet M input n |> Set.Finite.subset <| ReachableInAtMost_subset_ReachableSet M input n

/-
The number of bounded configurations is at most the size of the configuration space.
-/
lemma Card_BoundedConfig_Le_ConfigSpaceSize_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ) (input : List σ) :
  Nat.card { c | BoundedConfig M S input c } ≤ ConfigSpaceSize M S := by
    -- By definition of `ConfigSpaceSize`, it is the product of the cardinalities of the state space, the position space, and the tape space.
    apply Card_BoundedConfig_Le_ConfigSpaceSize M S input

/-
The set of possible next configurations is finite.
-/
lemma FiniteNextConfigs_Proof {k : ℕ} [NeZero k] (M : TuringMachine k σ) (c : Configuration k σ M.V) :
  Set.Finite (NextConfigs M c) := by
    exact?

/-
The set of configurations reachable in n+1 steps is the union of those reachable in n steps and their successors.
-/
lemma ReachableSet_Succ_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) :
  { c | ReachableInAtMost M (InitialConfig M input) c (n + 1) } =
  { c | ReachableInAtMost M (InitialConfig M input) c n } ∪
  { c' | ∃ c, ReachableInAtMost M (InitialConfig M input) c n ∧ step M c c' } := by
    -- By definition of ReachableInAtMost, we can split the set into two parts: those that are reachable in n steps and those that are reachable in n+1 steps but not in n steps.
    apply ReachableSet_Succ

/-
The number of configurations reachable in 0 steps is 1.
-/
lemma ReachableCount_Zero_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) :
  ReachableCount M input 0 = 1 := by
    exact?

/-
Reflexive transitive closure is equivalent to existence of a chain.
-/
lemma ReflTransGen_iff_ListChain_Proof {α : Type} (R : α → α → Prop) (a b : α) :
  Relation.ReflTransGen R a b ↔ ∃ l : List α, l.Chain' R ∧ l.head? = some a ∧ l.getLast? = some b := by
    exact?

/-
If there exists a chain from a to b, there exists a minimal length chain from a to b.
-/
lemma Exists_Minimal_Chain_Proof {α : Type} (R : α → α → Prop) (a b : α) :
  (∃ l : List α, l.Chain' R ∧ l.head? = some a ∧ l.getLast? = some b) →
  ∃ l : List α, l.Chain' R ∧ l.head? = some a ∧ l.getLast? = some b ∧
    ∀ l' : List α, l'.Chain' R → l'.head? = some a → l'.getLast? = some b → l.length ≤ l'.length := by
      intro l
      obtain ⟨l, hl⟩ := l
      have h_min : ∃ m ∈ {n : ℕ | ∃ l : List α, List.Chain' R l ∧ l.head? = some a ∧ l.getLast? = some b ∧ l.length = n}, ∀ n ∈ {n : ℕ | ∃ l : List α, List.Chain' R l ∧ l.head? = some a ∧ l.getLast? = some b ∧ l.length = n}, m ≤ n := by
        exact ⟨ Nat.find ⟨ _, ⟨ l, hl.1, hl.2.1, hl.2.2, rfl ⟩ ⟩, Nat.find_spec ( ⟨ _, ⟨ l, hl.1, hl.2.1, hl.2.2, rfl ⟩ ⟩ : ∃ n, ∃ l : List α, List.Chain' R l ∧ l.head? = some a ∧ l.getLast? = some b ∧ l.length = n ), fun n hn => Nat.find_min' _ hn ⟩
      generalize_proofs at *; (
      rcases h_min with ⟨ m, ⟨ l, hl₁, hl₂, hl₃, rfl ⟩, hm ⟩ ; exact ⟨ l, hl₁, hl₂, hl₃, fun l' hl₁' hl₂' hl₃' => hm _ ⟨ l', hl₁', hl₂', hl₃', rfl ⟩ ⟩ ;)

/-
The length of a Nodup list of elements satisfying P is at most the cardinality of {x | P x}.
-/
lemma Nodup_List_Length_Le_Card_Proof {α : Type} (P : α → Prop) [DecidablePred P] (l : List α)
  (h_nodup : l.Nodup) (h_subset : ∀ x ∈ l, P x) (h_finite : Set.Finite {x | P x}) :
  l.length ≤ Nat.card {x | P x} := by
    have h_card_le : l.toFinset.card ≤ Nat.card {x | P x} := by
      rw [ ← Nat.card_eq_finsetCard ];
      apply_rules [ Nat.card_mono ];
      exact fun x hx => h_subset x <| List.mem_toFinset.mp hx;
    rwa [ List.toFinset_card_of_nodup h_nodup ] at h_card_le

/-
If the Immerman construction exists, then NSPACE is closed under complementation.
-/
theorem NSPACE_Closed_Under_Complement_Conditional_Proof_2
  (h_construct : Immerman_Construction_Exists_Prop)
  {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (S : ℕ → ℕ) (hS : ∀ n, S n ≥ Nat.log2 n) (L : Set (List σ)) :
  InNSPACE S L → InNSPACE (fun n => 10 * S n) (LanguageComplement L) := by
    have := @NSPACE_Closed_Under_Complement_Conditional_Thm h_construct σ;
    convert this S hS L

/-
The number of configurations reachable in 0 steps is 1.
-/
lemma ReachableCount_Zero_Thm {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) :
  ReachableCount M input 0 = 1 := by
    -- The set of configurations reachable in 0 steps is just the initial configuration, so its cardinality is 1. We can use the fact that the cardinality of a singleton set is 1.
    have h_singleton : { c | ReachableInAtMost M (InitialConfig M input) c 0 } = { InitialConfig M input } := by
      exact ReachableInAtMost_Zero M input;
    rw [ ReachableCount, h_singleton ] ; aesop

/-
If there is a chain, there is a simple chain.
-/
lemma ListChain_imp_NodupListChain_Proof {α : Type} [DecidableEq α] (R : α → α → Prop) (a b : α) :
  (∃ l : List α, l.Chain' R ∧ l.head? = some a ∧ l.getLast? = some b) →
  ∃ l : List α, l.Chain' R ∧ l.head? = some a ∧ l.getLast? = some b ∧ l.Nodup := by
    intro h
    obtain ⟨l, hl_chain, hl_head, hl_last⟩ := h
    obtain ⟨l', hl'_chain, hl'_head, hl'_last, hl'_min⟩ : ∃ l' : List α, l'.Chain' R ∧ l'.head? = some a ∧ l'.getLast? = some b ∧ ∀ l'' : List α, l''.Chain' R → l''.head? = some a → l''.getLast? = some b → l'.length ≤ l''.length := by
      -- Apply the hypothesis `h_min` to obtain the minimal chain `l'`.
      apply Exists_Minimal_Chain R a b ⟨l, hl_chain, hl_head, hl_last⟩;
    refine' ⟨ l', hl'_chain, hl'_head, hl'_last, _ ⟩;
    apply_rules [ ShortestChain_is_Nodup ];
    grind

/-
A configuration is reachable if and only if it is reachable within a number of steps equal to the number of bounded configurations.
-/
lemma Reachable_iff_ReachableInAtMost_Max_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) (c : Configuration k σ M.V) :
  Reachable M (InitialConfig M input) c ↔
  ReachableInAtMost M (InitialConfig M input) c (Nat.card { x | BoundedConfig M (S input.length) input x }) := by
    exact?

/-
There exists a Turing machine that accepts all inputs.
-/
lemma Exists_Simple_TM_Proof {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ] :
  ∃ (k : ℕ) (hk : NeZero k) (M : TuringMachine k σ), ∀ x, AcceptsN M x ↔ True := by
    exact?

/-
A configuration is reachable iff it is reachable within MaxSteps.
-/
lemma Reachable_iff_ReachableInAtMost_MaxSteps_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) (c : Configuration k σ M.V) :
  Reachable M (InitialConfig M input) c ↔
  ReachableInAtMost M (InitialConfig M input) c (MaxSteps M (S input.length)) := by
    exact?

/-
The integer logarithm of a product is at most the sum of the logarithms plus one.
-/
lemma Nat.log2_mul_le_Proof (a b : ℕ) : Nat.log2 (a * b) ≤ Nat.log2 a + Nat.log2 b + 1 := by
  exact?

/-
The set of configurations with space bounded by S is finite.
-/
lemma FiniteBoundedConfig_Proof {k : ℕ} [NeZero k] (M : TuringMachine k σ) (S : ℕ) (input : List σ) :
  Set.Finite { c : Configuration k σ M.V | BoundedConfig M S input c } := by
    exact?

/-
If we know the size N of a finite set {x | P x}, we can prove that c does not satisfy P by exhibiting a subset S of size N where every element satisfies P, and c is not in S.
-/
lemma Set_Card_Certificate_Of_NonMembership_Proof {U : Type} (P : U → Prop) [DecidablePred P] (S_P : Set U) (hS_P : S_P = {x | P x}) (hFinite : S_P.Finite) (N : ℕ) (hN : Nat.card S_P = N) (c : U) :
  (¬ P c) ↔ ∃ (S : Set U), S.Finite ∧ Nat.card S = N ∧ S ⊆ S_P ∧ c ∉ S := by
    constructor;
    · grind;
    · rintro ⟨ S, hS₁, hS₂, hS₃, hS₄ ⟩;
      have h_card : Nat.card S = Nat.card S_P := by
        rw [ hS₂, hN ];
      have h_card : S = S_P := by
        apply_rules [ Set.eq_of_subset_of_ncard_le ];
        convert h_card.ge using 1;
      grind

/-
The condition that M does not accept input is equivalent to the existence of a count N and a set S of size N of reachable non-accepting configurations.
-/
lemma Immerman_Condition_Equivalence_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) :
  (¬ AcceptsN M input) ↔
  ∃ (N : ℕ), ReachableCount M input (MaxSteps M (S input.length)) = N ∧
  ∃ (S_set : Set (Configuration k σ M.V)),
    S_set ⊆ { c | Reachable M (InitialConfig M input) c } ∧
    Nat.card S_set = N ∧
    ∀ c ∈ S_set, c.state ≠ M.acceptState := by
      exact?

/-
Characterization of the step relation using NextConfig.
-/
lemma step_eq_NextConfig_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (c c' : Configuration k σ M.V) :
  step M c c' ↔ ∃ (r : Fin k → σ) (w : Fin (k-1) → σ) (m : Fin k → Move),
    (c.state, c'.state, r, w, m) ∈ M.edges ∧
    (∀ i, c.tapes i (c.positions i).toNat = r i) ∧
    c' = NextConfig c c'.state w m := by
      refine' ⟨ fun h => _, _ ⟩;
      · obtain ⟨ r, w, m, h1, h2, h3 ⟩ := h;
        use r, w, m;
        refine' ⟨ h1, h2, _ ⟩;
        unfold NextConfig;
        congr! 1;
        · ext i n; rcases i with ⟨ _ | i, hi ⟩ <;> simp_all +decide [ Fin.ext_iff ] ;
          split_ifs <;> simp_all +decide [ Fin.add_def, Nat.mod_eq_of_lt ];
          exact h3.1 ⟨ i, Nat.lt_pred_iff.mpr hi ⟩;
        · exact funext fun i => h3.2.2.1 i;
      · intro h
        obtain ⟨r, w, m, h_edge, h_read, h_config⟩ := h
        use r, w, m;
        refine' ⟨ h_edge, h_read, _, _, _, _ ⟩ <;> intro i <;> rw [ h_config ] <;> simp +decide [ NextConfig ];
        tauto

/-
The set of successor configurations is finite.
-/
lemma FiniteSuccessors_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (c : Configuration k σ M.V) :
  Set.Finite { c' | step M c c' } := by
    exact?

/-
If `l` is a chain starting at `a`, then every element in `l` is reachable from `a`.
-/
lemma Chain_implies_Reachable_Proof {α : Type} (R : α → α → Prop) (l : List α) (a : α) :
  l.Chain' R → l.head? = some a → ∀ x ∈ l, Relation.ReflTransGen R a x := by
    exact?

/-
If a chain has a duplicate, it can be shortened to a strictly shorter chain with the same endpoints.
-/
lemma Chain_shorten_of_duplicate_Proof {α : Type} (R : α → α → Prop) (l : List α)
  (h_chain : List.Chain' R l)
  (h_dup : ∃ i j : Fin l.length, i < j ∧ l.get i = l.get j) :
  ∃ l' : List α, List.Chain' R l' ∧ l'.head? = l.head? ∧ l'.getLast? = l.getLast? ∧ l'.length < l.length := by
    exact?

/-
If a chain is a shortest chain between its endpoints, it has no duplicates.
-/
lemma ShortestChain_is_Nodup_Proof {α : Type} (R : α → α → Prop) (l : List α)
  (h_chain : l.Chain' R)
  (h_min : ∀ l' : List α, l'.Chain' R → l'.head? = l.head? → l'.getLast? = l.getLast? → l.length ≤ l'.length) :
  l.Nodup := by
    exact?

/-
The number of configurations reachable in 0 steps is 1.
-/
lemma ReachableCount_Zero_Proof_2 {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) :
  ReachableCount M input 0 = 1 := by
    convert ReachableCount_Zero_Thm M input using 1

/-
If we know the number of reachable configurations, we can certify non-reachability by exhibiting that many reachable configurations and showing the target is not among them.
-/
lemma NotReachable_Checkable_Proof {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) (N : ℕ) :
  ReachableCount M input n = N →
  ∀ c, ¬ ReachableInAtMost M (InitialConfig M input) c n ↔
  ∃ (S : Set (Configuration k σ M.V)),
    S.Finite ∧
    Nat.card S = N ∧
    (∀ s ∈ S, ReachableInAtMost M (InitialConfig M input) s n) ∧
    c ∉ S := by
      exact?

/-
Definition of Deterministic Turing Machine and DSPACE complexity class.
-/
def Deterministic {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] (M : TuringMachine k σ) : Prop :=
  ∀ c c1 c2, step M c c1 → step M c c2 → c1 = c2

def InDSPACE {σ : Type} [DecidableEq σ] [Inhabited σ] (S : ℕ → ℕ) (L : Set (List σ)) : Prop :=
  ∃ (k : ℕ) (hk : NeZero k) (M : TuringMachine k σ),
    Deterministic M ∧ @SpaceBounded k σ _ hk M S ∧ @LanguageRecognizedByN σ _ k hk M = L

/-
Definition of TimeBounded Turing Machine and DTIME complexity class.
-/
def TimeBounded {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] (M : TuringMachine k σ) (T : ℕ → ℕ) : Prop :=
  ∀ input, ∀ path : List (Configuration k σ M.V),
    path.head? = some (InitialConfig M input) →
    path.Chain' (step M) →
    path.length ≤ T input.length + 1

def InDTIME {σ : Type} [DecidableEq σ] [Inhabited σ] (T : ℕ → ℕ) (L : Set (List σ)) : Prop :=
  ∃ (k : ℕ) (hk : NeZero k) (M : TuringMachine k σ),
    Deterministic M ∧ TimeBounded M T ∧ @LanguageRecognizedByN σ _ k hk M = L

/-
Definition of Symmetric Turing Machine and SL complexity class (renamed Symmetric to SymmetricTM to avoid conflict).
-/
def SymmetricTM {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] (M : TuringMachine k σ) : Prop :=
  ∀ c1 c2, step M c1 c2 → step M c2 c1

def InSL {σ : Type} [DecidableEq σ] [Inhabited σ] (S : ℕ → ℕ) (L : Set (List σ)) : Prop :=
  ∃ (k : ℕ) (hk : NeZero k) (M : TuringMachine k σ),
    SymmetricTM M ∧ @SpaceBounded k σ _ hk M S ∧ @LanguageRecognizedByN σ _ k hk M = L

/-
The set of configurations reachable in 0 steps is exactly the singleton set containing the initial configuration.
-/
theorem ReachableInAtMost_Zero_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) :
  { c | ReachableInAtMost M (InitialConfig M input) c 0 } = { InitialConfig M input } := by
    convert ReachableInAtMost_Zero M input using 1

/-
Monotonicity of ReachableInAtMost.
-/
theorem ReachableInAtMost_Mono_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (c1 c2 : Configuration k σ M.V) (n : ℕ) :
  ReachableInAtMost M c1 c2 n → ReachableInAtMost M c1 c2 (n + 1) := by
    -- Apply the monotonicity lemma to conclude the proof.
    apply ReachableInAtMost_Mono M c1 c2 n

/-
If c is reachable in at most n steps and c -> c', then c' is reachable in at most n+1 steps.
-/
theorem ReachableInAtMost_Step_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) (c c' : Configuration k σ M.V) (n : ℕ) :
  ReachableInAtMost M (InitialConfig M input) c n → step M c c' →
  ReachableInAtMost M (InitialConfig M input) c' (n + 1) := by
    exact?

/-
If a configuration is reachable in at most n+1 steps, it is either reachable in at most n steps or it is a successor of a configuration reachable in at most n steps.
-/
theorem ReachableInAtMost_Succ_Imp_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) (c' : Configuration k σ M.V) (n : ℕ) :
  ReachableInAtMost M (InitialConfig M input) c' (n + 1) →
  ReachableInAtMost M (InitialConfig M input) c' n ∨
  ∃ c, ReachableInAtMost M (InitialConfig M input) c n ∧ step M c c' := by
    have := @ReachableInAtMost_Succ_Imp_Proof;
    exact this M input c' n

/-
The set of configurations reachable in n+1 steps is the union of those reachable in n steps and their successors.
-/
theorem ReachableSet_Succ_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) :
  { c | ReachableInAtMost M (InitialConfig M input) c (n + 1) } =
  { c | ReachableInAtMost M (InitialConfig M input) c n } ∪
  { c' | ∃ c, ReachableInAtMost M (InitialConfig M input) c n ∧ step M c c' } := by
    exact?

/-
The set of edges in the Turing machine is finite.
-/
lemma FiniteEdges_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) : Set.Finite M.edges := by
    exact?

/-
The set of possible next configurations derived from edges is finite.
-/
lemma FiniteNextConfigs_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (c : Configuration k σ M.V) :
  Set.Finite (NextConfigs M c) := by
    exact Set.Finite.image _ ( FiniteEdges_ATP M )

/-
Characterization of the step relation using NextConfig.
-/
lemma step_eq_NextConfig_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (c c' : Configuration k σ M.V) :
  step M c c' ↔ ∃ (r : Fin k → σ) (w : Fin (k-1) → σ) (m : Fin k → Move),
    (c.state, c'.state, r, w, m) ∈ M.edges ∧
    (∀ i, c.tapes i (c.positions i).toNat = r i) ∧
    c' = NextConfig c c'.state w m := by
      exact?

/-
The set of configurations reachable in at most n steps is finite.
-/
lemma Finite_ReachableInAtMost_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) :
  Set.Finite { c | ReachableInAtMost M (InitialConfig M input) c n } := by
    have := @Finite_ReachableInAtMost_Proof k _ σ _ _ _ M input n; aesop;

/-
If a subset of a finite set has the same cardinality, it is equal to the set.
-/
lemma Set_eq_of_subset_of_card_eq_finite {α : Type} {s t : Set α} (ht : t.Finite) (hsub : s ⊆ t) (hcard : Nat.card s = Nat.card t) : s = t := by
  apply Set.eq_of_subset_of_ncard_le;
  · assumption;
  · aesop;
  · exact ht

/-
If the count of configurations reachable in n steps is N_prev, then the count of configurations reachable in n+1 steps is the size of the set of configurations c such that there exists a witness set S of size N_prev of reachable-in-n configurations, where c is either in S or a successor of S.
-/
theorem Count_Next_Step_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (n : ℕ) (N_prev : ℕ) :
  ReachableCount M input n = N_prev →
  ReachableCount M input (n + 1) =
  Nat.card { c | ∃ (S : Set (Configuration k σ M.V)),
    S.Finite ∧ Nat.card S = N_prev ∧
    (∀ s ∈ S, ReachableInAtMost M (InitialConfig M input) s n) ∧
    (c ∈ S ∨ ∃ s ∈ S, step M s c) } := by
      convert @Count_Next_Step_Thm k _ σ _ _ _ M input n N_prev

/-
If Ns is a valid count sequence, then the i-th element of Ns is the number of configurations reachable in at most i steps.
-/
theorem ValidCountSequence_Correct_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (Ns : List ℕ) :
  ValidCountSequence M input Ns →
  ∀ i : Fin Ns.length, Ns.get i = ReachableCount M input i := by
    exact?

/-
Existence of an Immerman witness implies rejection.
-/
theorem ImmermanWitness_Imp_NotAccepts {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) (Ns : List ℕ) (S_final : Set (Configuration k σ M.V)) :
  ImmermanWitness M S hS input Ns S_final → ¬ AcceptsN M input := by
    intro h
    obtain ⟨h_valid, h_count, h_S_final⟩ := h;
    -- By definition of `ValidCountSequence`, we know that `Ns.getLast!` is the number of configurations reachable in at most `MaxSteps M (S input.length)` steps.
    have h_last : Ns.getLast! = ReachableCount M input (MaxSteps M (S input.length)) := by
      convert ValidCountSequence_Correct M input Ns h_valid ⟨ Ns.length - 1, _ ⟩;
      all_goals norm_num [ h_count ];
      grind;
    -- By definition of `ReachableCount`, we know that `ReachableCount M input (MaxSteps M (S input.length))` is the number of configurations reachable in at most `MaxSteps M (S input.length)` steps.
    have h_reachable_count : Nat.card { c | ReachableInAtMost M (InitialConfig M input) c (MaxSteps M (S input.length)) } = ReachableCount M input (MaxSteps M (S input.length)) := by
      unfold ReachableCount; aesop;
    have h_S_final_eq : S_final = { c | ReachableInAtMost M (InitialConfig M input) c (MaxSteps M (S input.length)) } := by
      apply Set_eq_of_subset_of_card_eq_finite;
      · exact?;
      · exact fun c hc => h_S_final.2.1 c hc |> fun h => by simpa using h;
      · grind;
    intro h_accept
    obtain ⟨c, hc⟩ := h_accept
    have h_c_in_S_final : c ∈ S_final := by
      rw [h_S_final_eq] at *; exact (Reachable_iff_ReachableInAtMost_MaxSteps_Proof M S hS input c).mp hc.left;
    have h_c_not_accept : c.state ≠ M.acceptState := by
      exact h_S_final.2.2 c h_c_in_S_final
    exact h_c_not_accept (by
    exact hc.2)

/-
There exists a valid count sequence of length m+1 ending in the correct count.
-/
theorem Exists_ValidCountSequence_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (input : List σ) (m : ℕ) :
  ∃ Ns, Ns.length = m + 1 ∧ ValidCountSequence M input Ns ∧ Ns.getLast! = ReachableCount M input m := by
    refine' ⟨ List.ofFn fun i : Fin ( m + 1 ) => ReachableCount M input i, _, _, _ ⟩ <;> simp +decide [ Fin.add_def, Fin.last ];
    · constructor;
      · exact List.cons_ne_nil _ _;
      · refine' ⟨ _, _ ⟩;
        · convert ReachableCount_Zero_Thm M input;
        · intro i;
          rcases i with ⟨ _ | i, hi ⟩ <;> norm_num [ List.get! ] at hi ⊢;
          · rw [ show ReachableCount M input 1 = Nat.card { c : Configuration k σ M.V | ∃ S : Set ( Configuration k σ M.V ), S.Finite ∧ S.ncard = ReachableCount M input 0 ∧ ( ∀ s ∈ S, ReachableInAtMost M ( InitialConfig M input ) s 0 ) ∧ ( c ∈ S ∨ ∃ s ∈ S, step M s c ) } from ?_ ] ; aesop;
            convert Count_Next_Step_ATP M input 0 _ rfl using 1;
          · rw [ if_pos hi, if_pos ( Nat.lt_of_succ_lt hi ) ];
            convert Count_Next_Step M input ( i + 1 ) ( ReachableCount M input ( i + 1 ) ) rfl using 1;
    · grind

/-
If M does not accept, there exists an Immerman witness.
-/
theorem NotAccepts_Imp_ImmermanWitness {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) :
  ¬ AcceptsN M input → ∃ Ns S_final, ImmermanWitness M S hS input Ns S_final := by
    intro h_not_accepts
    set m := MaxSteps M (S input.length) with hm_def
    obtain ⟨Ns, hNs_length, hNs_valid, hNs_last⟩ : ∃ Ns : List ℕ, Ns.length = m + 1 ∧ ValidCountSequence M input Ns ∧ Ns.getLast! = ReachableCount M input m := Exists_ValidCountSequence_ATP M input m
    set S_final := { c : Configuration k σ M.V | ReachableInAtMost M (InitialConfig M input) c m } with hS_final_def
    have h_card_S_final : Nat.card S_final = Ns.getLast! := by
      exact hNs_last.symm ▸ rfl
    have h_subset_S_final : ∀ c ∈ S_final, c.state ≠ M.acceptState := by
      intros c hc h_accept
      have h_reachable : Reachable M (InitialConfig M input) c := by
        exact?
      have h_accepts : AcceptsN M input := by
        exact ⟨ c, h_reachable, h_accept ⟩
      contradiction
    use Ns, S_final;
    constructor <;> aesop

/-
A Turing machine M rejects an input if and only if there exists an Immerman witness.
-/
theorem ImmermanWitness_Theorem_ATP {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (input : List σ) :
  (¬ AcceptsN M input) ↔ ∃ Ns S_final, ImmermanWitness M S hS input Ns S_final := by
    exact?

/-
If the Immerman construction exists, then NSPACE is closed under complementation.
-/
theorem NSPACE_Closed_Under_Complement_Conditional_Proof_3
  (h_construct : Immerman_Construction_Exists_Prop)
  {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (S : ℕ → ℕ) (hS : ∀ n, S n ≥ Nat.log2 n) (L : Set (List σ)) :
  InNSPACE S L → InNSPACE (fun n => 10 * S n) (LanguageComplement L) := by
    convert NSPACE_Closed_Under_Complement_Conditional_Thm h_construct S hS L using 1

/-
The existence of an Immerman witness can be verified in NSPACE(O(S)).
-/
lemma ImmermanWitness_Verifiable_In_NSPACE {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (M : TuringMachine k σ) (S : ℕ → ℕ) (hS : SpaceBounded M S) (hS_log : ∀ n, S n ≥ Nat.log2 n) :
  InNSPACE (fun n => 10 * S n) { input | ∃ Ns S_final, ImmermanWitness M S hS input Ns S_final } := by
    convert NSPACE_Closed_Under_Complement_Conditional_Proof_3 _ _ _ _;
    any_goals assumption;
    any_goals exact { input | ¬AcceptsN M input };
    · constructor <;> intro h;
      · convert NSPACE_Closed_Under_Complement_Conditional_Proof_3 _ _ _ _ using 1;
        · exact?;
        · infer_instance;
        · infer_instance;
        · assumption;
      · have := @NSPACE_Closed_Under_Complement_Conditional_Proof_3;
        convert this ( by exact? ) S hS_log _ _ using 1;
        any_goals exact { input | AcceptsN M input };
        · ext input; simp [LanguageComplement, ImmermanWitness_Theorem_ATP];
          exact?;
        · infer_instance;
        · infer_instance;
        · exact ⟨ k, inferInstance, M, hS, rfl ⟩;
    · exact?

/-
Definitions of NL and coNL using Big-O notation for space bounds.
-/
def InNSPACE_O {σ : Type} [DecidableEq σ] [Inhabited σ] (f : ℕ → ℕ) (L : Set (List σ)) : Prop :=
  ∃ c > 0, InNSPACE (fun n => c * f n) L

def InCoNSPACE_O {σ : Type} [DecidableEq σ] [Inhabited σ] (f : ℕ → ℕ) (L : Set (List σ)) : Prop :=
  ∃ c > 0, InCoNSPACE (fun n => c * f n) L

def NL {σ : Type} [DecidableEq σ] [Inhabited σ] (L : Set (List σ)) : Prop :=
  InNSPACE_O (fun n => Nat.log2 n) L

def coNL {σ : Type} [DecidableEq σ] [Inhabited σ] (L : Set (List σ)) : Prop :=
  InCoNSPACE_O (fun n => Nat.log2 n) L

/-
The Immerman construction exists (proven using the witness theorem).
-/
theorem Immerman_Construction_Exists_Proven : Immerman_Construction_Exists_Prop := by
  -- Apply the lemma that states the existence of the Immerman construction for any Turing machine M, space bound S, and logarithmic bound hS_log.
  apply Immerman_Construction_Exists

/-
Definition of IsStuck: a state u and read symbols r are stuck if there are no outgoing edges.
-/
def IsStuck {k : ℕ} [NeZero k] {σ : Type} [DecidableEq σ] [Inhabited σ]
  (M : TuringMachine k σ) (u : M.V) (r : Fin k → σ) : Prop :=
  ∀ v w m, (u, v, r, w, m) ∉ M.edges

/-
Swapping the accept and reject states of a Turing machine creates a new machine.
-/
def SwapStates {k : ℕ} {σ : Type} (M : TuringMachine k σ) : TuringMachine k σ :=
  { M with
    acceptState := M.rejectState
    rejectState := M.acceptState }

/-
If a Turing machine is space-bounded, then the machine obtained by swapping its accept and reject states is also space-bounded.
-/
lemma SwapStates_SpaceBounded {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (S : ℕ → ℕ) :
  SpaceBounded M S → SpaceBounded (SwapStates M) S := by
    unfold SpaceBounded at * ; aesop

/-
If the swapped machine accepts in co-NSPACE, then the original machine does not accept in NSPACE, assuming accepting states are terminal and distinct from rejecting states.
-/
lemma SwapStates_AcceptsCoN_imp_Not_AcceptsN {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ)
  (h_disjoint : M.acceptState ≠ M.rejectState)
  (h_terminal_accept : ∀ c, Reachable M (InitialConfig M input) c → c.state = M.acceptState → Terminal M c) :
  AcceptsCoN (SwapStates M) input → ¬ AcceptsN M input := by
    intro h1 h2
    obtain ⟨c, hc_reachable, hc_state⟩ := h2
    have hc_terminal : Terminal M c := h_terminal_accept c hc_reachable hc_state
    have hc_swap_state : c.state = M.rejectState := by
      exact?;
    exact h_disjoint ( hc_state.symm.trans hc_swap_state )

/-
If a Turing machine does not accept an input in NSPACE, and all its terminal reachable configurations are either accepting or rejecting, then the swapped machine accepts the input in co-NSPACE.
-/
lemma Not_AcceptsN_imp_SwapStates_AcceptsCoN {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ)
  (h_terminal_states : ∀ c, Reachable M (InitialConfig M input) c → Terminal M c → c.state = M.acceptState ∨ c.state = M.rejectState) :
  ¬ AcceptsN M input → AcceptsCoN (SwapStates M) input := by
    unfold AcceptsN at *; aesop;

/-
If a Turing machine has the property that accepting states are terminal and all terminal states are either accepting or rejecting (and distinct), then the swapped machine accepts in co-NSPACE iff the original rejects in NSPACE.
-/
lemma SwapStates_AcceptsCoN_iff_Not_AcceptsN {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ)
  (h_disjoint : M.acceptState ≠ M.rejectState)
  (h_terminal_accept : ∀ c, Reachable M (InitialConfig M input) c → c.state = M.acceptState → Terminal M c)
  (h_terminal_states : ∀ c, Reachable M (InitialConfig M input) c → Terminal M c → c.state = M.acceptState ∨ c.state = M.rejectState) :
  AcceptsCoN (SwapStates M) input ↔ ¬ AcceptsN M input := by
    constructor;
    · exact?;
    · exact?

/-
A Turing machine is "good" on an input if its accept and reject states are distinct, reaching the accept state implies termination, and every terminal reachable configuration is either in the accept or reject state.
-/
def GoodTM {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k] (M : TuringMachine k σ) (input : List σ) : Prop :=
  M.acceptState ≠ M.rejectState ∧
  (∀ c, Reachable M (InitialConfig M input) c → c.state = M.acceptState → Terminal M c) ∧
  (∀ c, Reachable M (InitialConfig M input) c → Terminal M c → c.state = M.acceptState ∨ c.state = M.rejectState)

/-
Definition of a normalized Turing machine that wraps an existing machine to ensure well-behaved accept/reject states.
-/
def NormalizedTM {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) : TuringMachine k σ :=
  haveI : Fintype M.V := M.fintypeV
  haveI : DecidableEq M.V := M.decV
  let V' := Sum M.V (Fin 2)
  let startState' : V' := Sum.inl M.startState
  let acceptState' : V' := Sum.inr 0
  let rejectState' : V' := Sum.inr 1
  let keep_w (r : Fin k → σ) : Fin (k-1) → σ := fun i => r ⟨i.val + 1, by omega⟩
  let original_edges : Set (V' × V' × (Fin k → σ) × (Fin (k-1) → σ) × (Fin k → Move)) :=
    { e | ∃ (u v : M.V) (r : Fin k → σ) (w : Fin (k-1) → σ) (m : Fin k → Move),
          e = (Sum.inl u, Sum.inl v, r, w, m) ∧ (u, v, r, w, m) ∈ M.edges }
  let accept_edges : Set (V' × V' × (Fin k → σ) × (Fin (k-1) → σ) × (Fin k → Move)) :=
    { e | ∃ (u : M.V) (r : Fin k → σ), u = M.acceptState ∧
          e = (Sum.inl u, acceptState', r, keep_w r, fun _ => Move.Stay) }
  let reject_edges : Set (V' × V' × (Fin k → σ) × (Fin (k-1) → σ) × (Fin k → Move)) :=
    { e | ∃ (u : M.V) (r : Fin k → σ), u ≠ M.acceptState ∧ IsStuck M u r ∧
          e = (Sum.inl u, rejectState', r, keep_w r, fun _ => Move.Stay) }
  { V := V',
    decV := inferInstance,
    fintypeV := inferInstance,
    edges := original_edges ∪ accept_edges ∪ reject_edges,
    startState := startState',
    acceptState := acceptState',
    rejectState := rejectState' }

/-
Any configuration reachable in the normalized Turing machine corresponds to a reachable configuration in the original machine, either directly (if in a Sum.inl state) or by having the same positions (if in a Sum.inr state).
-/
lemma NormalizedTM_Reachable_StrongCorrespondence {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ) (c' : Configuration k σ (NormalizedTM M).V) :
  Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) c' →
  ((∃ u, c'.state = Sum.inl u ∧ ∃ c, Reachable M (InitialConfig M input) c ∧ c.state = u ∧ c.tapes = c'.tapes ∧ c.positions = c'.positions) ∨
   (∃ x, c'.state = Sum.inr x ∧ ∃ c, Reachable M (InitialConfig M input) c ∧ c'.positions = c.positions)) := by
     intro hc';
     induction hc';
     · exact Or.inl ⟨ M.startState, rfl, InitialConfig M input, by constructor, rfl, rfl, rfl ⟩;
     · rename_i h₁ h₂ h;
       unfold step at h₂;
       rcases h with ( ⟨ u, hu, c, hc, hc', hc'', hc''' ⟩ | ⟨ x, hx, c, hc, hc' ⟩ ) <;> simp_all +decide [ NormalizedTM ];
       rcases h₂ with ⟨ r, w, m, h₂, h, h₄, h₅, h₆ ⟩ ; rcases h₂ with ( ( ⟨ u', v, ⟨ rfl, hv ⟩, h₂ ⟩ | ⟨ hu, hv, rfl, rfl ⟩ ) | ⟨ hu, hv, hv', rfl, rfl ⟩ ) <;> simp_all +decide [ Reachable ] ;
       · use NextConfig c v w m;
         refine' ⟨ _, _, _, _ ⟩;
         · convert hc.tail _ using 1;
           use r, w, m;
           unfold NextConfig; aesop;
         · exact?;
         · ext i; simp [NextConfig, h];
           rcases i with ⟨ _ | i, hi ⟩ <;> simp_all +decide [ Fin.ext_iff ];
           grind;
         · ext i; simp +decide [ *, NextConfig ] ;
       · use c; aesop;
       · use c;
         aesop

/-
If a Turing machine is space-bounded, then its normalized version (with distinct accept/reject states) is also space-bounded by the same function.
-/
lemma NormalizedTM_SpaceBounded {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (S : ℕ → ℕ) :
  SpaceBounded M S → SpaceBounded (NormalizedTM M) S := by
    intro hM c hc hc';
    -- By `NormalizedTM_Reachable_StrongCorrespondence`, there exists a configuration `c'` reachable in `M` such that `hc.positions = c'.positions`.
    obtain ⟨c', hc'_reachable, hc'_positions⟩ : ∃ c' : Configuration k σ M.V, Reachable M (InitialConfig M c) c' ∧ hc.positions = c'.positions := by
      have := NormalizedTM_Reachable_StrongCorrespondence M c hc hc';
      grind;
    aesop

/-
The normalized Turing machine accepts an input in NSPACE if and only if the original machine accepts it.
-/
lemma NormalizedTM_AcceptsN_iff {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ) :
  AcceptsN (NormalizedTM M) input ↔ AcceptsN M input := by
    apply Iff.intro
    intro h_accepts_normalized
    obtain ⟨c', hc'_reachable, hc'_accept⟩ : ∃ c', Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) c' ∧ c'.state = Sum.inr 0 := by
      exact h_accepts_normalized
    generalize_proofs at *; (
    -- Since $c'$ is in state $Sum �.in�r 0$, it must have been reached from $Sum.inl M.acceptState$.
    obtain ⟨c', hc'_reachable, hc'_accept⟩ : ∃ c', Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) c' ∧ c'.state = Sum.inl M.acceptState := by
      obtain ⟨c'', hc''_reachable, hc''_accept⟩ : ∃ c'', Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) c'' ∧ c''.state = Sum.inr 0 ∧ c''.state = Sum.inr 0 := by
        aesop
        skip
      generalize_proofs at *; (
      induction' hc''_reachable with c'' hc''_reachable ih <;> simp_all +decide [ Reachable ];
      · cases hc''_accept;
      · rename_i h₁ h₂ h
        generalize_proofs at *; (
        unfold step at h₂; simp_all +decide [ NormalizedTM ] ;
        grind))
    generalize_proofs at *; (
    have := NormalizedTM_Reachable_StrongCorrespondence M input c' hc'_reachable; simp_all +decide [ AcceptsN ] ;
    grind +ring));
    intro h_accept
    obtain ⟨c, hc⟩ := h_accept;
    -- Since $c$ is reachable in $M$, we can construct a path in $NormalizedTM M$ that reaches $Sum.in �l� c$.
    have h_path : Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) (Configuration.mk (Sum.inl c.state) c.tapes c.positions) := by
      have h_path : ∀ c, Reachable M (InitialConfig M input) c → Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) (Configuration.mk (Sum.inl c.state) c.tapes c.positions) := by
        intro c hc
        induction' hc with c' hc' ih;
        · constructor;
        · rename_i h₁ h₂ h;
          obtain ⟨ u, v, r, w, m, huv, h ⟩ := h₂;
          apply_rules [ Relation.ReflTransGen.tail ];
          constructor;
          exact ⟨ v, r, by exact Or.inl <| Or.inl ⟨ c'.state, hc'.state, u, v, r, rfl, w ⟩, m, huv, h ⟩
      generalize_proofs at *; (exact h_path c hc.1);
    -- Since there's an edge from Sum.inl � M�.acceptState to Sum.inr 0, we can extend the path to reach Sum.inr 0.
    have h_edge : step (NormalizedTM M) (Configuration.mk (Sum.inl M.acceptState) c.tapes c.positions) (Configuration.mk (Sum.inr 0) c.tapes c.positions) := by
      unfold step NormalizedTM; aesop;
    -- By combining the paths, we can conclude that Sum.inr 0 � is� reachable from the initial configuration.
    have h_combined : Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) (Configuration.mk (Sum.inr 0) c.tapes c.positions) := by
      have h_step : step (NormalizedTM M) (Configuration.mk (Sum.inl c.state) c.tapes c.positions) (Configuration.mk (Sum.inr 0) c.tapes c.positions) := by
        aesop
      exact h_path.tail h_step;
    exact ⟨ _, h_combined, rfl ⟩

/-
The normalized Turing machine satisfies the "GoodTM" properties: distinct accept/reject states, accepting implies terminal, and all terminal states are either accepting or rejecting.
-/
lemma NormalizedTM_GoodTM {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ) :
  GoodTM (NormalizedTM M) input := by
    refine' ⟨ _, _, _ ⟩;
    · unfold NormalizedTM; aesop;
    · unfold Terminal;
      unfold step;
      unfold NormalizedTM at * ; aesop;
    · intro c hc hterm;
      contrapose! hterm;
      -- If the state is neither accept nor reject, then there must be some edge from this state.
      have h_edge : ∃ v w m, (c.state, v, fun i => c.tapes i (c.positions i).toNat, w, m) ∈ (NormalizedTM M).edges := by
        cases c : c.state <;> simp_all +decide [ NormalizedTM ];
        · exact Classical.or_iff_not_imp_right.2 fun h' => by unfold IsStuck at h'; aesop;
        · rename_i x; fin_cases x <;> contradiction;
      obtain ⟨ v, w, m, h ⟩ := h_edge;
      refine' fun h' => _;
      unfold Terminal at h';
      simp_all +decide [ step ];
      specialize h' ( NextConfig c v w m ) ( fun i => c.tapes i ( c.positions i ).toNat ) w m h ; simp_all +decide [ NextConfig ]

/-
A configuration in the normalized Turing machine is terminal if and only if its state is one of the new accept or reject states (Sum.inr 0 or Sum.inr 1).
-/
lemma NormalizedTM_Terminal_iff {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (c' : Configuration k σ (NormalizedTM M).V) :
  Terminal (NormalizedTM M) c' ↔ c'.state = Sum.inr 0 ∨ c'.state = Sum.inr 1 := by
    constructor <;> intro h;
    · -- By definition of terminal, if c' is terminal, then there are no edges starting from c'.state.
      by_contra h_contra;
      -- Since `c'.state` is not � `�Sum.inr 0` or `Sum.inr 1`, it must be `Sum.inl u` for some `u`.
      obtain ⟨u, hu⟩ : ∃ u, c'.state = Sum.inl u := by
        have h_sum_inl : ∀ x : (NormalizedTM M).V, x ≠ Sum.inr 0 ∧ x ≠ Sum.inr 1 → ∃ u, x = Sum.inl u := by
          intros x hx
          cases x <;> simp_all +decide;
          rename_i x; fin_cases x <;> tauto;
        exact h_sum_inl _ ⟨ by tauto, by tauto ⟩;
      -- By definition of terminal, if c' is terminal, then there are no edges starting from c'.state. Since c'.state is Sum.inl u, we need to check if there are any edges starting from u.
      by_cases hu_accept : u = M.acceptState;
      · unfold Terminal at h; simp_all +decide [ Terminal ] ;
        contrapose! h;
        unfold step;
        use Configuration.mk (Sum.inr 0) c'.tapes c'.positions;
        unfold NormalizedTM; aesop;
      · by_cases hu_stuck : IsStuck M u (fun i => c'.tapes i (c'.positions i).toNat);
        · unfold Terminal at h;
          simp_all +decide [ step ];
          specialize h (Configuration.mk (Sum.inr 1) c'.tapes c'.positions) (fun i => c'.tapes i (c'.positions i).toNat) (fun i => c'.tapes ⟨i.val + 1, by omega⟩ (c'.positions ⟨i.val + 1, by omega⟩).toNat) (fun _ => Move.Stay) ; simp_all +decide [ NormalizedTM ];
        · unfold Terminal at h; simp_all +decide [ Terminal ] ;
          obtain ⟨ v, w, m, hv ⟩ : ∃ v w m, ( u, v, fun i => c'.tapes i ( c'.positions i ).toNat, w, m ) ∈ M.edges := by
            unfold IsStuck at hu_stuck; aesop;
          refine' h ( NextConfig c' ( Sum.inl v ) w m ) _;
          constructor;
          use w, m;
          unfold NormalizedTM; simp +decide [ hu, hv ] ;
          unfold NextConfig; simp +decide [ hu ] ;
          tauto;
    · cases h <;> simp +decide [ *, Terminal ];
      · intro x hx; obtain ⟨ u, v, r, w, m, e_eq, he ⟩ := hx; simp_all +decide [ NormalizedTM ] ;
      · unfold step;
        unfold NormalizedTM; aesop;

/-
If a configuration is reachable in the original Turing machine, its corresponding "lifted" configuration (wrapped in Sum.inl) is reachable in the normalized Turing machine.
-/
lemma NormalizedTM_Reachable_Lift {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ) (c : Configuration k σ M.V) :
  Reachable M (InitialConfig M input) c →
  Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) (Configuration.mk (Sum.inl c.state) c.tapes c.positions) := by
    intro hc;
    -- By definition of NormalizedTM, the edges of the normalized machine include the original edges of M, but with the states wrapped in Sum.inl.
    have h_edges : ∀ u v r w m, (u, v, r, w, m) ∈ M.edges → (Sum.inl u, Sum.inl v, r, w, m) ∈ (NormalizedTM M).edges := by
      intro u v r w m h
      simp [NormalizedTM, h];
    induction hc;
    · constructor;
    · rename_i c' hc' ih;
      convert ih.tail _;
      obtain ⟨ r, w, m, h₁, h₂, h₃ ⟩ := hc';
      exact ⟨ r, w, m, h_edges _ _ _ _ _ h₁, h₂, by aesop ⟩

/-
If the normalized Turing machine accepts an input in co-NSPACE, then the original machine also accepts it in co-NSPACE.
-/
lemma NormalizedTM_AcceptsCoN_imp_AcceptsCoN {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ) :
  AcceptsCoN (NormalizedTM M) input → AcceptsCoN M input := by
    contrapose!;
    unfold AcceptsCoN;
    simp +zetaDelta at *;
    intro c hc hterm hneq
    obtain ⟨c', hc', hterm'⟩ : ∃ c', Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) c' ∧ c'.state = Sum.inr 1 ∧ c'.positions = c.positions := by
      have h_reach : Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) (Configuration.mk (Sum.inl c.state) c.tapes c.positions) := by
        exact?;
      -- Since `c` is � terminal� in `M`, there are no edges in `M` from `c`. Thus, there are no "original edges" from `c'` in `NormalizedTM M`.
      have h_no_original_edges : ¬∃ v w m, (Sum.inl c.state, Sum.inl v, fun i => c.tapes i (c.positions i).toNat, w, m) ∈ (NormalizedTM M).edges := by
        unfold NormalizedTM at *; simp_all +decide [ Terminal ] ;
        intro v w m h; specialize hterm ( NextConfig c v w m ) ; simp_all +decide [ step ] ;
        specialize hterm _ _ _ h ; simp_all +decide [ NextConfig ];
      -- Since `c` is terminal in `M`, there are no edges in `M` from `c`. Thus, there are no "original edges" from `c'` in `NormalizedTM M`. The only possible edges from `c'` are "accept edges" or "reject edges".
      have h_reject_edge : (Sum.inl c.state, Sum.inr 1, fun i => c.tapes i (c.positions i).toNat, fun i => c.tapes ⟨i.val + 1, by omega⟩ (c.positions ⟨i.val + 1, by omega⟩).toNat, fun _ => Move.Stay) ∈ (NormalizedTM M).edges := by
        unfold NormalizedTM at *; aesop;
      have h_reach_reject : Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) (NextConfig { state := Sum.inl c.state, tapes := c.tapes, positions := c.positions } (Sum.inr 1) (fun i => c.tapes ⟨i.val + 1, by omega⟩ (c.positions ⟨i.val + 1, by omega⟩).toNat) (fun _ => Move.Stay)) := by
                                                                                                                    apply Relation.ReflTransGen.tail h_reach;
                                                                                                                    constructor;
                                                                                                                    rotate_left;
                                                                                                                    exact fun i => c.tapes i ( c.positions i |> Int.toNat );
                                                                                                                    unfold NextConfig; aesop;
      refine' ⟨ _, h_reach_reject, _, _ ⟩ <;> simp +decide [ NextConfig ];
      exact funext fun _ => by simp +decide [ Move.toInt ] ;
    refine' ⟨ c', hc', _, _ ⟩ <;> simp_all +decide [ Terminal ];
    · intro x hx; unfold step at hx; simp_all +decide [ NormalizedTM ] ;
    · simp +decide [ NormalizedTM ]

/-
If the normalized Turing machine reaches the reject state (Sum.inr 1), then the original machine must have reached a stuck, non-accepting configuration.
-/
lemma NormalizedTM_Reachable_Reject_Imp_Reachable_Stuck {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ) (c' : Configuration k σ (NormalizedTM M).V) :
  Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) c' →
  c'.state = Sum.inr 1 →
  ∃ c, Reachable M (InitialConfig M input) c ∧ c.state ≠ M.acceptState ∧ IsStuck M c.state (fun i => c.tapes i (c.positions i).toNat) := by
    intro hc' hc'_state
    obtain ⟨c_prev, hc_prev, hc'_prev⟩ : ∃ c_prev, Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) c_prev ∧ step (NormalizedTM M) c_prev c' := by
      induction hc' <;> tauto;
    -- By definition of `reject_edges`, since `c_prev` � leads� to `c'` with `c'.state = Sum.inr 1`, there must exist a `u` such that `c_prev.state = Sum.inl u`, `u ≠ M.acceptState`, and `IsStuck M u fun i => c_prev.tapes i (c_prev.positions i).toNat`.
    obtain ⟨u, hu⟩ : ∃ u : M.V, c_prev.state = Sum.inl u ∧ u ≠ M.acceptState ∧ IsStuck M u (fun i => c_prev.tapes i (c_prev.positions i).toNat) := by
      unfold step at hc'_prev;
      unfold NormalizedTM at hc'_prev; aesop;
    -- By definition of `reject_edges`, since `c_prev` leads to ` �c�'` with `c'.state = Sum.inr 1`, there must exist a `c` in `M` such that `c.state = u`, `c.tapes = c_prev.tapes`, and `c.positions = c_prev.positions`.
    obtain ⟨c, hc⟩ : ∃ c : Configuration k σ M.V, Reachable M (InitialConfig M input) c ∧ c.state = u ∧ c.tapes = c_prev.tapes ∧ c.positions = c_prev.positions := by
      have := NormalizedTM_Reachable_StrongCorrespondence M input c_prev hc_prev;
      grind;
    use c; aesop;

/-
If the original Turing machine accepts an input in co-NSPACE, then the normalized Turing machine also accepts it in co-NSPACE.
-/
lemma AcceptsCoN_imp_NormalizedTM_AcceptsCoN {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ) :
  AcceptsCoN M input → AcceptsCoN (NormalizedTM M) input := by
    intro h;
    unfold AcceptsCoN at *;
    intro c hc hcterminal; have := NormalizedTM_Terminal_iff M c; simp_all +decide [ Terminal ] ;
    -- Since `c` is reachable and terminal in `NormalizedTM M`, by `NormalizedTM_Reachable_Reject_Imp_Reachable_Stuck`, there exists `c'` reachable in `M` such that `c'.state ≠ M.acceptState` and `IsStuck M � c�'.state ...`.
    by_cases h_case : c.state = Sum.inr 1;
    · -- By `NormalizedTM_Reachable_Reject_I �mp�_Reachable_Stuck`, there exists `c'` reachable in `M` such that `c'.state ≠ M.acceptState` and `IsStuck M c'.state ...`.
      obtain ⟨c', hc', hc'_state, hc'_stuck⟩ : ∃ c' : Configuration k σ M.V, Reachable M (InitialConfig M input) c' ∧ c'.state ≠ M.acceptState ∧ IsStuck M c'.state (fun i => c'.tapes i (c'.positions i).toNat) := by
        exact?;
      contrapose! h;
      refine' ⟨ c', hc', _, hc'_state ⟩;
      intro x hx; have := hc'_stuck x.state; unfold step at hx; aesop;
    · exact this.resolve_right h_case

/-
If a Turing machine configuration is stuck (no valid transitions for the current state and tape symbols), then it is terminal.
-/
lemma IsStuck_Imp_Terminal {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (c : Configuration k σ M.V) :
  IsStuck M c.state (fun i => c.tapes i (c.positions i).toNat) → Terminal M c := by
    intro h;
    unfold Terminal;
    unfold step;
    contrapose! h; aesop;

/-
If the normalized Turing machine reaches the reject state, that configuration is terminal.
-/
lemma NormalizedTM_Reject_Terminal {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ) (c : Configuration k σ (NormalizedTM M).V) :
  Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) c →
  c.state = (NormalizedTM M).rejectState →
  Terminal (NormalizedTM M) c := by
    intros hc hc_reject
    have h_terminal : c.state = (NormalizedTM M).rejectState → Terminal (NormalizedTM M) c := by
      intros hc_reject
      apply NormalizedTM_Terminal_iff M c |>.2;
      exact Or.inr hc_reject;
    exact h_terminal hc_reject

/-
The complexity class NSPACE(O(f)) is closed under complementation, provided f(n) >= log n.
-/
theorem InNSPACE_O_Closed_Under_Complement
  {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (f : ℕ → ℕ) (hf : ∀ n, f n ≥ Nat.log2 n) (L : Set (List σ)) :
  InNSPACE_O f L → InNSPACE_O f (LanguageComplement L) := by
    intro hL
    obtain ⟨c, hc_pos, hc⟩ := hL
    obtain ⟨M, hM⟩ := hc
    have hS : ∀ n, f n ≥ Nat.log2 n := by
      assumption
    have h_compl : InNSPACE (fun n => 10 * (c * f n)) (LanguageComplement L) := by
      apply NSPACE_Closed_Under_Complement_Conditional;
      · exact?;
      · exact fun n => le_trans ( hS n ) ( le_mul_of_one_le_left' hc_pos );
      · exact ⟨ M, hM.choose, hM.choose_spec.choose, hM.choose_spec.choose_spec.1, hM.choose_spec.choose_spec.2 ⟩
    have h_final : InNSPACE_O f (LanguageComplement L) := by
      exact ⟨ 10 * c, by positivity, by simpa [ mul_assoc, mul_comm, mul_left_comm ] using h_compl ⟩
    exact h_final

/-
For the normalized Turing machine, accepting in co-NSPACE is equivalent to not accepting in NSPACE with the accept/reject states swapped.
-/
lemma NormalizedTM_AcceptsCoN_iff_Not_AcceptsN_SwapStates {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ) :
  AcceptsCoN (NormalizedTM M) input ↔ ¬ AcceptsN (SwapStates (NormalizedTM M)) input := by
    apply Iff.intro;
    · intro h;
      apply SwapStates_AcceptsCoN_imp_Not_AcceptsN;
      · unfold SwapStates NormalizedTM; aesop;
      · have h_terminal : ∀ c', Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) c' → c'.state = (NormalizedTM M).rejectState → Terminal (NormalizedTM M) c' := by
          exact?;
        unfold SwapStates at *; aesop;
      · convert h using 1;
    · intro h_not_accept
      have h_terminal : ∀ c, Reachable (NormalizedTM M) (InitialConfig (NormalizedTM M) input) c → Terminal (NormalizedTM M) c → c.state = (NormalizedTM M).acceptState := by
        intro c hc hc_terminal
        have h_state : c.state = (NormalizedTM M).acceptState ∨ c.state = (NormalizedTM M).rejectState := by
          apply (NormalizedTM_GoodTM M input).2.2 c hc hc_terminal;
        contrapose! h_not_accept;
        use c;
        aesop;
      exact?

/-
Reachability is preserved under swapping states because the transition relation (edges) remains unchanged.
-/
lemma SwapStates_Reachable {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (c1 c2 : Configuration k σ M.V) :
  Reachable (SwapStates M) c1 c2 ↔ Reachable M c1 c2 := by
    constructor <;> intro h <;> induction h <;> tauto;

/-
The normalized Turing machine accepts an input in co-NSPACE if and only if the original machine accepts it.
-/
lemma NormalizedTM_AcceptsCoN_iff {k : ℕ} {σ : Type} [DecidableEq σ] [Inhabited σ] [NeZero k]
  (M : TuringMachine k σ) (input : List σ) :
  AcceptsCoN (NormalizedTM M) input ↔ AcceptsCoN M input := by
    apply Iff.intro;
    · exact?;
    · exact?

/-
The complexity classes NSPACE(O(f)) and co-NSPACE(O(f)) are equal, provided f(n) >= log n.
-/
theorem InNSPACE_O_eq_InCoNSPACE_O
  {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ]
  (f : ℕ → ℕ) (hf : ∀ n, f n ≥ Nat.log2 n) (L : Set (List σ)) :
  InNSPACE_O f L ↔ InCoNSPACE_O f L := by
    refine' ⟨ _, _ ⟩ <;> intro h;
    · -- By definition of $InNSPACE_O �$,� there exists some constant $c > 0$ such that $InNSPACE (fun n => c * f n) L$.
      obtain ⟨c, hc_pos, hc⟩ := h;
      -- By definition of $InNSPACE_O$, there exists some constant $c > 0$ such that $InNSPACE (fun n => c * f n) (LanguageComplement L)$.
      obtain ⟨c', hc'_pos, hc'⟩ : ∃ c' > 0, InNSPACE (fun n => c' * f n) (LanguageComplement L) := by
        have := InNSPACE_O_Closed_Under_Complement f ( fun n => hf n ) L ⟨ c, hc_pos, hc ⟩;
        exact this;
      use c';
      obtain ⟨ k, hk, M, hM ⟩ := hc';
      refine' ⟨ hc'_pos, k, hk, SwapStates ( NormalizedTM M ), _, _ ⟩ <;> simp_all +decide [ LanguageRecognizedByN, LanguageRecognizedByCoN ];
      · exact SwapStates_SpaceBounded _ _ ( NormalizedTM_SpaceBounded _ _ hM.1 );
      · ext input; specialize hM; have := hM.2; simp_all +decide [ Set.ext_iff, LanguageComplement ] ;
        have h_swap : AcceptsCoN (SwapStates (NormalizedTM M)) input ↔ ¬ AcceptsN (NormalizedTM M) input := by
          apply SwapStates_AcceptsCoN_iff_Not_AcceptsN;
          · exact ne_of_apply_ne ( fun x => x ) ( by simp +decide [ NormalizedTM ] );
          · exact fun c hc hc' => by rw [ NormalizedTM_Terminal_iff ] ; aesop;
          · exact fun c hc₁ hc₂ => by have := NormalizedTM_Terminal_iff M c; aesop;
        have h_normalized : AcceptsN (NormalizedTM M) input ↔ AcceptsN M input := by
          exact?;
        aesop;
    · -- By definition of `InCoNSPACE_O �`, � there exists a machine `M` and a constant `c` such that `M` accepts `L` in co-NSPACE with space bound `c * f`.
      obtain ⟨c, hc_pos, hM⟩ := h;
      obtain ⟨M, hM⟩ := hM;
      -- By definition of `LanguageRecognizedByCoN �`,� there exists a Turing machine `M'` and a constant `c'` such that `M'` accepts `L` in co-NSPACE with space bound `c' * f`.
      obtain ⟨hk, M', hM', hL⟩ := hM;
      -- By definition of `LanguageRecognizedByCoN`, there exists a Turing machine `M'` and a constant `c'` such that `M'` accepts `L` in co-NSPACE with space bound `c' * f`. Since `LanguageRecognizedByCoN M' = L`, we have `LanguageRecognizedByN (SwapStates (NormalizedTM M')) = L`.
      have hL_swap : LanguageRecognizedByN (SwapStates (NormalizedTM M')) = LanguageComplement L := by
        have hL_swap : ∀ input, AcceptsCoN (NormalizedTM M') input ↔ ¬ AcceptsN (SwapStates (NormalizedTM M')) input := by
          apply NormalizedTM_AcceptsCoN_iff_Not_AcceptsN_SwapStates;
        have hL_swap : ∀ input, AcceptsCoN (NormalizedTM M') input ↔ AcceptsCoN M' input := by
          exact?;
        unfold LanguageRecognizedByN LanguageRecognizedByCoN LanguageComplement at *; aesop;
      -- Since `LanguageRecognizedByN (SwapStates (NormalizedTM M')) = LanguageComplement L`, we have `InNSPACE_O f (LanguageComplement L)`.
      have hL_complement : InNSPACE_O f (LanguageComplement L) := by
        use c;
        refine' ⟨ hc_pos, _, _ ⟩;
        exact M;
        refine' ⟨ hk, SwapStates ( NormalizedTM M' ), _, _ ⟩;
        · exact SwapStates_SpaceBounded _ _ ( NormalizedTM_SpaceBounded _ _ hM' );
        · exact hL_swap;
      convert InNSPACE_O_Closed_Under_Complement f hf ( LanguageComplement L ) hL_complement using 1;
      exact Set.ext fun x => by simp +decide [ LanguageComplement ] ;

/-
The complexity class NL is equal to co-NL.
-/
theorem NL_eq_coNL {σ : Type} [DecidableEq σ] [Inhabited σ] [Fintype σ] (L : Set (List σ)) :
  NL L ↔ coNL L := by
    convert InNSPACE_O_eq_InCoNSPACE_O _ _ _ using 1;
    · infer_instance;
    · exact fun n => le_rfl
