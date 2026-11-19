/- Nano/V2Self/Proof/ParInvGlue: box C's EXPRESSION-CORE handlers with their side conditions discharged from the Layer-2 invariants
`WF` (B: ghost operand / binding counts, SInv), `CInv` (C: modes, flatten frames on top, stash before letPairSemi) and `DInv` (F: `.defs`
only alone).  `h_core`: for every expression-core frame, a running machine step is a `stepF` step that keeps `Rep`. -/
import Nano.V2Self.Proof.ParInvLetPair
import Nano.V2Self.Proof.ParInvPrimary
import Nano.V2Self.Proof.ParRunWF
import Nano.V2Self.Proof.ParRunCInv
import Nano.V2Self.Proof.ParRunSmall
namespace ParInv
open C BufL ParSpec ParRun

/-- the frames handled here (tasks 1–9, 11, 12, 40–42, 49–53, 90) -/
def _root_.ParRun.Frame.isCore : Frame → Bool
  | .expr .. | .binLoop _ | .prim _ | .rparen | .mkBin _ | .ifCmp _ | .ifThen .. | .ifElse | .mkIte _ | .letSemi .. | .letEnd ..
  | .parenClose | .letStart _ | .mkPair | .shiftNum _ | .letPairX _ | .letPairY .. | .stash _ | .letPairSemi .. | .tupRest => true
  | _ => false

theorem isFlat_eq (f : Frame) : f.isFlat = f.isFl := by cases f <;> rfl

theorem ghost_top {c : Ctx} {f : Frame} {fs : List Frame} {g : G} (h : (effL c (f :: fs) g).isSome = true) :
    (effF c f g).isSome = true := by
  simp only [effL] at h
  cases e : effF c f g with
  | none => rw [e] at h; simp at h
  | some _ => rfl

theorem noflat_of {f : Frame} {fs : List Frame} {st : St} (hC : CInv (f :: fs, st)) (hf : f.isFl = false) :
    fs.all (fun g => !g.isFlat) = true := by
  have := cinv_noflat hC hf
  simpa [isFlat_eq] using this

theorem indef_of {f : Frame} {fs : List Frame} {st : St} (hD : DInv (f :: fs, st)) (hf : f ≠ .defs) : inDefF fs = true := by
  have := defs_not_below hD hf
  simp only [inDefF, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  intro g hg
  cases g <;> simp [Frame.isDefs] <;> exact this _ hg rfl

/-- **expression core**: every expression-core frame steps like `stepF` and keeps `Rep`, under WF ∧ CInv ∧ DInv ∧ Small -/
theorem h_core {h ts : Buf} {st : St} {f : Frame} {fs : List Frame} (r : Rep h ts st (f :: fs)) (hcore : f.isCore = true)
    (hW : WF (f :: fs) st) (hC : CInv (f :: fs, st)) (hD : DInv (f :: fs, st)) (hSm : Small (f :: fs, st))
    (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF f st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  have gt := ghost_top hW.ghost
  have hv1 : ∀ g : G, (if 1 ≤ g.v then some g else none : Option G).isSome = true → 1 ≤ g.v := by
    intro g e; by_cases q : 1 ≤ g.v
    · exact q
    · simp [q] at e
  cases f with
  | expr m md => exact h_expr r hs
  | binLoop m =>
    simp only [effF] at gt
    have := hv1 _ gt; simp only [St.g] at this
    exact h_binLoop r (fun e => by rw [e] at this; simp at this) hs
  | prim md => exact h_prim r (cinv_mode hC) (indef_of hD (by simp)) (noflat_of hC rfl) hs
  | rparen => exact h_rparen r hs
  | mkBin op => exact h_mkBin r (noflat_of hC rfl) hs
  | ifCmp tl => exact h_ifCmp r hs
  | ifThen c tl => exact h_ifThen r hs
  | ifElse => exact h_ifElse r hs
  | mkIte c => exact h_mkIte r (noflat_of hC rfl) hs
  | letSemi x tl =>
    simp only [effF] at gt
    have := hv1 _ gt; simp only [St.g] at this
    exact h_letSemi r (fun e => by rw [e] at this; simp at this) hSm.1 hSm.2.2.2.2.2.1 hs
  | letEnd s d =>
    simp only [effF, St.g] at gt
    have hd : d ≤ st.binds.length := by
      by_cases q : 2 ≤ st.vals.length ∧ d ≤ st.binds.length
      · exact q.2
      · simp [q] at gt
    exact h_letEnd r hd (noflat_of hC rfl) hs
  | parenClose => exact h_parenClose r hs
  | letStart tl => exact h_letStart r hs
  | mkPair =>
    simp only [effF, St.g] at gt
    have hv2 : 2 ≤ st.vals.length := by
      by_cases q : 2 ≤ st.vals.length
      · exact q
      · simp [q] at gt
    exact h_mkPair r (noflat_of hC rfl) hv2 hW.inv.1 hSm.2.2.2.2.2.1 hs
  | shiftNum op => exact h_shiftNum r (noflat_of hC rfl) hs
  | letPairX tl => exact h_letPairX r hs
  | letPairY x tl => exact h_letPairY r hs
  | stash x => exact h_stash r hs
  | letPairSemi y tl =>
    simp only [effF] at gt
    have := hv1 _ gt; simp only [St.g] at this
    exact h_letPairSemi r (fun e => by rw [e] at this; simp at this) (cinv_stash hC) hSm.1 hSm.2.2.2.2.2.1 hs
  | tupRest => exact h_tupRest r hs
  | _ => simp [Frame.isCore] at hcore

end ParInv
