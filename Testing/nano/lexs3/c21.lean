import Compiler.S3.Front
import Nano.LexS3
import Nano.S3Stage

s3_enc Nano.Tok
namespace Nano.LS
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace LexA
open Proven.S3
abbrev S : Proven.S3.Sig := ⟨[[[], [.w, (.d 0)]], [[], [(.d 2)]], [[.b, (.d 3)]], [[], [(.d 4), (.d 3)]], [[], [], [.b], [(.d 0)], [.w], [], [], [], [], [], [], [], []], [[], [(.d 5)]], [[], [(.d 3)]], [[(.d 0), (.d 0)]], [[], [(.d 4)]], [[], [.b]]], [([(.d 0)], (.d 0)), ([(.d 1)], (.d 0)), ([(.d 3)], (.d 0)), ([(.d 0), (.d 0)], (.d 0)), ([(.d 4)], (.d 0)), ([(.d 0)], (.d 0)), ([.w], (.d 0)), ([(.d 0)], (.d 1)), ([(.d 0)], .b), ([.w], .b), ([.w], .b), ([.w], .b), ([(.d 5), (.d 0)], (.d 6)), ([(.d 0)], .b), ([(.d 4), (.d 6)], (.d 6)), ([(.d 5), (.d 0)], (.d 7)), ([.w, (.d 7)], (.d 7)), ([(.d 0)], (.d 8)), ([(.d 0)], .b), ([.w, (.d 0)], .w), ([(.d 0)], .b), ([(.d 0)], .b), ([(.d 0)], .b), ([(.d 0)], .b), ([(.d 0)], .b), ([(.d 0)], .b), ([(.d 0)], .b), ([(.d 0)], (.d 5)), ([(.d 5), (.d 5)], (.d 5)), ([(.d 9), (.d 3)], (.d 1)), ([.w], (.d 9)), ([.w, (.d 3)], .w), ([(.d 4)], .w)]⟩
def b0 : Proven.S3.Expr S [(.d 0)] (.d 0) :=
  (.let_ (σ := (.d 1)) (.call ⟨7, by decide⟩ (.cons .z .nil) rfl) (.call ⟨1, by decide⟩ (.cons .z .nil) rfl))
def b1 : Proven.S3.Expr S [(.d 1)] (.d 0) :=
  (.cas (i := 1) .z (Alts.arms (.cons (.mk 0 0 .nil) (.cons (.cas (i := 2) .z (Alts.arms (.cons (.let_ (σ := .w) (.let_ (σ := .b) (.var .z) (.ite .z (.lit 2) (.lit 1))) (.let_ (σ := (.d 0)) (.call ⟨2, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) .nil))) .nil))))
def b2 : Proven.S3.Expr S [(.d 3)] (.d 0) :=
  (.cas (i := 3) .z (Alts.arms (.cons (.mk 0 0 .nil) (.cons (.let_ (σ := (.d 0)) (.call ⟨4, by decide⟩ (.cons .z .nil) rfl) (.let_ (σ := (.d 0)) (.call ⟨2, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.call ⟨3, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))) .nil))))
def b3 : Proven.S3.Expr S [(.d 0), (.d 0)] (.d 0) :=
  (.cas (i := 0) .z (Alts.arms (.cons (.var (.s .z)) (.cons (.let_ (σ := (.d 0)) (.call ⟨3, by decide⟩ (.cons (.s .z) (.cons (.s (.s (.s .z))) .nil)) rfl) (.mk 0 1 (.cons (.s .z) (.cons .z .nil)))) .nil))))
def b4 : Proven.S3.Expr S [(.d 4)] (.d 0) :=
  (.cas (i := 4) .z (Alts.arms (.cons (.let_ (σ := .w) (.lit 1) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.cons (.let_ (σ := .w) (.lit 2) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.cons (.ite .z (.let_ (σ := .w) (.lit 4) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.let_ (σ := .w) (.lit 3) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil)))))) (.cons (.let_ (σ := .w) (.lit 14) (.let_ (σ := (.d 0)) (.call ⟨5, by decide⟩ (.cons (.s .z) .nil) rfl) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.cons (.let_ (σ := .w) (.lit 5) (.let_ (σ := (.d 0)) (.call ⟨6, by decide⟩ (.cons (.s .z) .nil) rfl) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.cons (.let_ (σ := .w) (.lit 6) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.cons (.let_ (σ := .w) (.lit 7) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.cons (.let_ (σ := .w) (.lit 8) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.cons (.let_ (σ := .w) (.lit 9) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.cons (.let_ (σ := .w) (.lit 10) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.cons (.let_ (σ := .w) (.lit 11) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.cons (.let_ (σ := .w) (.lit 12) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.cons (.let_ (σ := .w) (.lit 13) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) .nil)))))))))))))))
def b5 : Proven.S3.Expr S [(.d 0)] (.d 0) :=
  (.cas (i := 0) .z (Alts.arms (.cons (.let_ (σ := .w) (.lit 0) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.cons (.let_ (σ := .w) (.lit 1) (.let_ (σ := (.d 0)) (.let_ (σ := (.d 0)) (.call ⟨5, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.mk 0 1 (.cons (.s (.s .z)) (.cons .z .nil)))) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) .nil))))
def b6 : Proven.S3.Expr S [.w] (.d 0) :=
  (.let_ (σ := .w) (.let_ (σ := .w) (.lit 255) (.bin (.op .and) (.s .z) .z)) (.let_ (σ := (.d 0)) (.let_ (σ := .w) (.let_ (σ := .w) (.let_ (σ := .w) (.lit 8) (.bin (.op .lshr) (.s (.s .z)) .z)) (.let_ (σ := .w) (.lit 255) (.bin (.op .and) (.s .z) .z))) (.let_ (σ := (.d 0)) (.let_ (σ := .w) (.let_ (σ := .w) (.let_ (σ := .w) (.lit 16) (.bin (.op .lshr) (.s (.s (.s .z))) .z)) (.let_ (σ := .w) (.lit 255) (.bin (.op .and) (.s .z) .z))) (.let_ (σ := (.d 0)) (.let_ (σ := .w) (.let_ (σ := .w) (.let_ (σ := .w) (.lit 24) (.bin (.op .lshr) (.s (.s (.s (.s .z)))) .z)) (.let_ (σ := .w) (.lit 255) (.bin (.op .and) (.s .z) .z))) (.let_ (σ := (.d 0)) (.let_ (σ := .w) (.let_ (σ := .w) (.let_ (σ := .w) (.lit 32) (.bin (.op .lshr) (.s (.s (.s (.s (.s .z))))) .z)) (.let_ (σ := .w) (.lit 255) (.bin (.op .and) (.s .z) .z))) (.let_ (σ := (.d 0)) (.let_ (σ := .w) (.let_ (σ := .w) (.let_ (σ := .w) (.lit 40) (.bin (.op .lshr) (.s (.s (.s (.s (.s (.s .z)))))) .z)) (.let_ (σ := .w) (.lit 255) (.bin (.op .and) (.s .z) .z))) (.let_ (σ := (.d 0)) (.let_ (σ := .w) (.let_ (σ := .w) (.let_ (σ := .w) (.lit 48) (.bin (.op .lshr) (.s (.s (.s (.s (.s (.s (.s .z))))))) .z)) (.let_ (σ := .w) (.lit 255) (.bin (.op .and) (.s .z) .z))) (.let_ (σ := (.d 0)) (.let_ (σ := .w) (.let_ (σ := .w) (.let_ (σ := .w) (.lit 56) (.bin (.op .lshr) (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))) .z)) (.let_ (σ := .w) (.lit 255) (.bin (.op .and) (.s .z) .z))) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.mk 0 1 (.cons (.s .z) (.cons .z .nil))))) (.mk 0 1 (.cons (.s .z) (.cons .z .nil)))))
def b7 : Proven.S3.Expr S [(.d 0)] (.d 1) :=
  (.let_ (σ := .b) (.call ⟨8, by decide⟩ (.cons .z .nil) rfl) (.ite .z (.let_ (σ := (.d 6)) (.let_ (σ := (.d 5)) (.call ⟨27, by decide⟩ (.cons (.s .z) .nil) rfl) (.call ⟨12, by decide⟩ (.cons .z (.cons (.s (.s .z)) .nil)) rfl)) (.cas (i := 6) .z (Alts.arms (.cons (.mk 1 0 .nil) (.cons (.let_ (σ := (.d 9)) (.let_ (σ := .w) (.let_ (σ := .w) (.lit 0) (.call ⟨31, by decide⟩ (.cons .z (.cons (.s .z) .nil)) rfl)) (.call ⟨30, by decide⟩ (.cons .z .nil) rfl)) (.call ⟨29, by decide⟩ (.cons .z (.cons (.s .z) .nil)) rfl)) .nil))))) (.mk 1 0 .nil)))
def b8 : Proven.S3.Expr S [(.d 0)] .b :=
  (.cas (i := 0) .z (Alts.arms (.cons (.blit true) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit true) (.cons (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.call ⟨9, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.ite .z (.blit true) (.let_ (σ := .w) (.lit 41) (.cmp .eq (.s (.s (.s (.s .z)))) .z)))) (.ite .z (.let_ (σ := .w) (.lit 40) (.cmp .eq (.s (.s .z)) .z)) (.blit false))) (.bnot .z)) (.ite .z (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 41) (.cmp .eq (.s (.s (.s (.s .z)))) .z)) (.ite .z (.call ⟨9, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.blit false))) (.bnot .z)) (.blit false))) (.ite .z (.call ⟨8, by decide⟩ (.cons (.s (.s (.s (.s .z)))) .nil) rfl) (.blit false))) .nil)))) .nil))))
def b9 : Proven.S3.Expr S [.w] .b :=
  (.let_ (σ := .b) (.call ⟨10, by decide⟩ (.cons .z .nil) rfl) (.ite .z (.blit true) (.call ⟨11, by decide⟩ (.cons (.s .z) .nil) rfl)))
def b10 : Proven.S3.Expr S [.w] .b :=
  (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 65) (.cmp .ule .z (.s .z))) (.ite .z (.let_ (σ := .w) (.lit 90) (.cmp .ule (.s (.s .z)) .z)) (.blit false))) (.ite .z (.blit true) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 97) (.cmp .ule .z (.s (.s .z)))) (.ite .z (.let_ (σ := .w) (.lit 122) (.cmp .ule (.s (.s (.s .z))) .z)) (.blit false))))) (.ite .z (.blit true) (.let_ (σ := .w) (.lit 95) (.cmp .eq (.s (.s .z)) .z))))
def b11 : Proven.S3.Expr S [.w] .b :=
  (.let_ (σ := .b) (.let_ (σ := .w) (.lit 48) (.cmp .ule .z (.s .z))) (.ite .z (.let_ (σ := .w) (.lit 57) (.cmp .ule (.s (.s .z)) .z)) (.blit false)))
def b12 : Proven.S3.Expr S [(.d 5), (.d 0)] (.d 6) :=
  (.cas (i := 5) .z (Alts.arms (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.let_ (σ := (.d 3)) (.mk 3 0 .nil) (.mk 6 1 (.cons .z .nil))) (.cons (.mk 6 0 .nil) .nil)))) (.cons (.cas (i := 0) (.s (.s .z)) (Alts.arms (.cons (.let_ (σ := (.d 3)) (.mk 3 0 .nil) (.mk 6 1 (.cons .z .nil))) (.cons (.let_ (σ := .b) (.let_ (σ := .w) (.lit 32) (.cmp .eq (.s .z) .z)) (.ite .z (.call ⟨12, by decide⟩ (.cons (.s (.s (.s .z))) (.cons (.s (.s .z)) .nil)) rfl) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 10) (.cmp .eq (.s (.s .z)) .z)) (.ite .z (.cas (i := 0) (.s (.s (.s .z))) (Alts.arms (.cons (.let_ (σ := (.d 3)) (.mk 3 0 .nil) (.mk 6 1 (.cons .z .nil))) (.cons (.let_ (σ := .b) (.let_ (σ := .w) (.lit 32) (.cmp .eq (.s .z) .z)) (.ite .z (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s .z))))))) (.cons (.s (.s (.s (.s (.s (.s .z)))))) .nil)) rfl) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 10) (.cmp .eq (.s (.s .z)) .z)) (.ite .z (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))) (.cons (.s (.s (.s (.s (.s (.s (.s .z))))))) .nil)) rfl) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 100) (.cmp .eq (.s (.s (.s .z))) .z)) (.ite .z (.cas (i := 0) (.s (.s (.s (.s .z)))) (Alts.arms (.cons (.mk 6 0 .nil) (.cons (.let_ (σ := .b) (.let_ (σ := .w) (.lit 101) (.cmp .eq (.s .z) .z)) (.ite .z (.cas (i := 0) (.s (.s .z)) (Alts.arms (.cons (.mk 6 0 .nil) (.cons (.let_ (σ := .b) (.let_ (σ := .w) (.lit 102) (.cmp .eq (.s .z) .z)) (.ite .z (.let_ (σ := .b) (.call ⟨13, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.ite .z (.mk 6 0 .nil) (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))))))))))) (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))))))))) .nil)) rfl))) (.mk 6 0 .nil))) .nil)))) (.mk 6 0 .nil))) .nil)))) (.mk 6 0 .nil))))))) .nil)))) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 40) (.cmp .eq (.s (.s (.s .z))) .z)) (.ite .z (.let_ (σ := (.d 4)) (.mk 4 5 .nil) (.let_ (σ := (.d 6)) (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s .z)))))) (.cons (.s (.s (.s (.s (.s .z))))) .nil)) rfl) (.call ⟨14, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 41) (.cmp .eq (.s (.s (.s (.s .z)))) .z)) (.ite .z (.let_ (σ := (.d 4)) (.mk 4 6 .nil) (.let_ (σ := (.d 6)) (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s .z))))))) (.cons (.s (.s (.s (.s (.s (.s .z)))))) .nil)) rfl) (.call ⟨14, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 43) (.cmp .eq (.s (.s (.s (.s (.s .z))))) .z)) (.ite .z (.let_ (σ := (.d 4)) (.mk 4 9 .nil) (.let_ (σ := (.d 6)) (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))) (.cons (.s (.s (.s (.s (.s (.s (.s .z))))))) .nil)) rfl) (.call ⟨14, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 45) (.cmp .eq (.s (.s (.s (.s (.s (.s .z)))))) .z)) (.ite .z (.cas (i := 0) (.s (.s (.s (.s (.s (.s (.s .z))))))) (Alts.arms (.cons (.let_ (σ := (.d 4)) (.mk 4 10 .nil) (.let_ (σ := (.d 6)) (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))) (.cons (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))) .nil)) rfl) (.call ⟨14, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))) (.cons (.let_ (σ := .b) (.let_ (σ := .w) (.lit 45) (.cmp .eq (.s .z) .z)) (.ite .z (.mk 6 0 .nil) (.let_ (σ := (.d 4)) (.mk 4 10 .nil) (.let_ (σ := (.d 6)) (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))))))) (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))))) .nil)) rfl) (.call ⟨14, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))))) .nil)))) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 42) (.cmp .eq (.s (.s (.s (.s (.s (.s (.s .z))))))) .z)) (.ite .z (.let_ (σ := (.d 4)) (.mk 4 11 .nil) (.let_ (σ := (.d 6)) (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))))) (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))) .nil)) rfl) (.call ⟨14, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 59) (.cmp .eq (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))) .z)) (.ite .z (.let_ (σ := (.d 4)) (.mk 4 12 .nil) (.let_ (σ := (.d 6)) (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))))) (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))))) .nil)) rfl) (.call ⟨14, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 58) (.cmp .eq (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))) .z)) (.ite .z (.cas (i := 0) (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))))) (Alts.arms (.cons (.let_ (σ := (.d 4)) (.mk 4 7 .nil) (.let_ (σ := (.d 6)) (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))))))) (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))))) .nil)) rfl) (.call ⟨14, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))) (.cons (.let_ (σ := .b) (.let_ (σ := .w) (.lit 61) (.cmp .eq (.s .z) .z)) (.ite .z (.let_ (σ := (.d 4)) (.mk 4 8 .nil) (.let_ (σ := (.d 6)) (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))))))))) (.cons (.s (.s (.s .z))) .nil)) rfl) (.call ⟨14, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))) (.let_ (σ := (.d 4)) (.mk 4 7 .nil) (.let_ (σ := (.d 6)) (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))))))))) (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))))))))) .nil)) rfl) (.call ⟨14, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))))) .nil)))) (.let_ (σ := .b) (.call ⟨9, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))) .nil) rfl) (.ite .z (.let_ (σ := (.d 7)) (.let_ (σ := (.d 0)) (.mk 0 1 (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))))) (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))))) .nil))) (.call ⟨15, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))))))) (.cons .z .nil)) rfl)) (.cas (i := 7) .z (Alts.arms (.cons (.let_ (σ := (.d 8)) (.call ⟨17, by decide⟩ (.cons .z .nil) rfl) (.cas (i := 8) .z (Alts.arms (.cons (.mk 6 0 .nil) (.cons (.let_ (σ := (.d 6)) (.call ⟨12, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))))))))))) (.cons (.s (.s (.s .z))) .nil)) rfl) (.call ⟨14, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl)) .nil))))) .nil)))) (.mk 6 0 .nil))))))))))))))))))))) .nil)))) .nil))))
def b13 : Proven.S3.Expr S [(.d 0)] .b :=
  (.cas (i := 0) .z (Alts.arms (.cons (.blit false) (.cons (.call ⟨9, by decide⟩ (.cons .z .nil) rfl) .nil))))
def b14 : Proven.S3.Expr S [(.d 4), (.d 6)] (.d 6) :=
  (.cas (i := 6) (.s .z) (Alts.arms (.cons (.mk 6 0 .nil) (.cons (.let_ (σ := (.d 3)) (.mk 3 1 (.cons (.s .z) (.cons .z .nil))) (.mk 6 1 (.cons .z .nil))) .nil))))
def b15 : Proven.S3.Expr S [(.d 5), (.d 0)] (.d 7) :=
  (.cas (i := 5) .z (Alts.arms (.cons (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 7 0 (.cons .z (.cons (.s (.s .z)) .nil)))) (.cons (.cas (i := 0) (.s (.s .z)) (Alts.arms (.cons (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.mk 7 0 (.cons (.s .z) (.cons .z .nil))))) (.cons (.let_ (σ := .b) (.call ⟨9, by decide⟩ (.cons .z .nil) rfl) (.ite .z (.let_ (σ := (.d 7)) (.call ⟨15, by decide⟩ (.cons (.s (.s (.s .z))) (.cons (.s (.s .z)) .nil)) rfl) (.call ⟨16, by decide⟩ (.cons (.s (.s .z)) (.cons .z .nil)) rfl)) (.let_ (σ := (.d 0)) (.mk 0 0 .nil) (.let_ (σ := (.d 0)) (.mk 0 1 (.cons (.s (.s .z)) (.cons (.s (.s (.s .z))) .nil))) (.mk 7 0 (.cons (.s .z) (.cons .z .nil))))))) .nil)))) .nil))))
def b16 : Proven.S3.Expr S [.w, (.d 7)] (.d 7) :=
  (.cas (i := 7) (.s .z) (Alts.arms (.cons (.let_ (σ := (.d 0)) (.mk 0 1 (.cons (.s (.s .z)) (.cons .z .nil))) (.mk 7 0 (.cons .z (.cons (.s (.s .z)) .nil)))) .nil)))
def b17 : Proven.S3.Expr S [(.d 0)] (.d 8) :=
  (.cas (i := 0) .z (Alts.arms (.cons (.mk 8 0 .nil) (.cons (.let_ (σ := .b) (.call ⟨11, by decide⟩ (.cons .z .nil) rfl) (.ite .z (.let_ (σ := .b) (.call ⟨18, by decide⟩ (.cons (.s (.s (.s .z))) .nil) rfl) (.ite .z (.let_ (σ := (.d 4)) (.let_ (σ := .w) (.let_ (σ := .w) (.lit 0) (.call ⟨19, by decide⟩ (.cons .z (.cons (.s (.s (.s (.s (.s .z))))) .nil)) rfl)) (.mk 4 4 (.cons .z .nil))) (.mk 8 1 (.cons .z .nil))) (.mk 8 0 .nil))) (.let_ (σ := .b) (.call ⟨20, by decide⟩ (.cons (.s (.s (.s .z))) .nil) rfl) (.ite .z (.let_ (σ := (.d 4)) (.mk 4 0 .nil) (.mk 8 1 (.cons .z .nil))) (.let_ (σ := .b) (.call ⟨22, by decide⟩ (.cons (.s (.s (.s (.s .z)))) .nil) rfl) (.ite .z (.let_ (σ := (.d 4)) (.mk 4 1 .nil) (.mk 8 1 (.cons .z .nil))) (.let_ (σ := .b) (.call ⟨23, by decide⟩ (.cons (.s (.s (.s (.s (.s .z))))) .nil) rfl) (.ite .z (.let_ (σ := (.d 4)) (.let_ (σ := .b) (.blit false) (.mk 4 2 (.cons .z .nil))) (.mk 8 1 (.cons .z .nil))) (.let_ (σ := .b) (.call ⟨24, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s .z)))))) .nil) rfl) (.ite .z (.let_ (σ := (.d 4)) (.let_ (σ := .b) (.blit true) (.mk 4 2 (.cons .z .nil))) (.mk 8 1 (.cons .z .nil))) (.let_ (σ := .b) (.call ⟨25, by decide⟩ (.cons (.s (.s (.s (.s (.s (.s (.s .z))))))) .nil) rfl) (.ite .z (.let_ (σ := (.d 4)) (.mk 4 3 (.cons (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))) .nil)) (.mk 8 1 (.cons .z .nil))) (.mk 8 0 .nil))))))))))))) .nil))))
def b18 : Proven.S3.Expr S [(.d 0)] .b :=
  (.cas (i := 0) .z (Alts.arms (.cons (.blit true) (.cons (.let_ (σ := .b) (.call ⟨11, by decide⟩ (.cons .z .nil) rfl) (.ite .z (.call ⟨18, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.blit false))) .nil))))
def b19 : Proven.S3.Expr S [.w, (.d 0)] .w :=
  (.cas (i := 0) (.s .z) (Alts.arms (.cons (.var .z) (.cons (.let_ (σ := .w) (.let_ (σ := .w) (.let_ (σ := .w) (.lit 10) (.bin .mul (.s (.s (.s .z))) .z)) (.let_ (σ := .w) (.let_ (σ := .w) (.var (.s .z)) (.let_ (σ := .w) (.lit 48) (.bin (.op .sub) (.s .z) .z))) (.bin (.op .add) (.s .z) .z))) (.call ⟨19, by decide⟩ (.cons .z (.cons (.s (.s .z)) .nil)) rfl)) .nil))))
def b20 : Proven.S3.Expr S [(.d 0)] .b :=
  (.cas (i := 0) .z (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 100) (.cmp .eq (.s (.s (.s (.s (.s .z))))) .z)) (.ite .z (.let_ (σ := .w) (.lit 101) (.cmp .eq (.s (.s (.s (.s .z)))) .z)) (.blit false))) (.ite .z (.let_ (σ := .w) (.lit 102) (.cmp .eq (.s (.s .z)) .z)) (.blit false))) (.ite .z (.call ⟨21, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.blit false))) .nil)))) .nil)))) .nil))))
def b21 : Proven.S3.Expr S [(.d 0)] .b :=
  (.cas (i := 0) .z (Alts.arms (.cons (.blit true) (.cons (.blit false) .nil))))
def b22 : Proven.S3.Expr S [(.d 0)] .b :=
  (.cas (i := 0) .z (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 108) (.cmp .eq (.s (.s (.s (.s (.s .z))))) .z)) (.ite .z (.let_ (σ := .w) (.lit 101) (.cmp .eq (.s (.s (.s (.s .z)))) .z)) (.blit false))) (.ite .z (.let_ (σ := .w) (.lit 116) (.cmp .eq (.s (.s .z)) .z)) (.blit false))) (.ite .z (.call ⟨21, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.blit false))) .nil)))) .nil)))) .nil))))
def b23 : Proven.S3.Expr S [(.d 0)] .b :=
  (.cas (i := 0) .z (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 85) (.cmp .eq (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))))) .z)) (.ite .z (.let_ (σ := .w) (.lit 73) (.cmp .eq (.s (.s (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))))) .z)) (.blit false))) (.ite .z (.let_ (σ := .w) (.lit 110) (.cmp .eq (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))) .z)) (.blit false))) (.ite .z (.let_ (σ := .w) (.lit 116) (.cmp .eq (.s (.s (.s (.s (.s (.s .z)))))) .z)) (.blit false))) (.ite .z (.let_ (σ := .w) (.lit 54) (.cmp .eq (.s (.s (.s (.s .z)))) .z)) (.blit false))) (.ite .z (.let_ (σ := .w) (.lit 52) (.cmp .eq (.s (.s .z)) .z)) (.blit false))) (.ite .z (.call ⟨21, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.blit false))) .nil)))) .nil)))) .nil)))) .nil)))) .nil)))) .nil))))
def b24 : Proven.S3.Expr S [(.d 0)] .b :=
  (.cas (i := 0) .z (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.cas (i := 0) (.s .z) (Alts.arms (.cons (.blit false) (.cons (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 73) (.cmp .eq (.s (.s (.s (.s (.s (.s (.s (.s (.s .z))))))))) .z)) (.ite .z (.let_ (σ := .w) (.lit 110) (.cmp .eq (.s (.s (.s (.s (.s (.s (.s (.s .z)))))))) .z)) (.blit false))) (.ite .z (.let_ (σ := .w) (.lit 116) (.cmp .eq (.s (.s (.s (.s (.s (.s .z)))))) .z)) (.blit false))) (.ite .z (.let_ (σ := .w) (.lit 54) (.cmp .eq (.s (.s (.s (.s .z)))) .z)) (.blit false))) (.ite .z (.let_ (σ := .w) (.lit 52) (.cmp .eq (.s (.s .z)) .z)) (.blit false))) (.ite .z (.call ⟨21, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.blit false))) .nil)))) .nil)))) .nil)))) .nil)))) .nil))))
def b25 : Proven.S3.Expr S [(.d 0)] .b :=
  (.cas (i := 0) .z (Alts.arms (.cons (.blit false) (.cons (.let_ (σ := .b) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 97) (.cmp .ule .z (.s .z))) (.ite .z (.let_ (σ := .w) (.lit 122) (.cmp .ule (.s (.s .z)) .z)) (.blit false))) (.ite .z (.call ⟨26, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.blit false))) .nil))))
def b26 : Proven.S3.Expr S [(.d 0)] .b :=
  (.cas (i := 0) .z (Alts.arms (.cons (.blit true) (.cons (.let_ (σ := .b) (.let_ (σ := .b) (.call ⟨11, by decide⟩ (.cons .z .nil) rfl) (.ite .z (.blit true) (.let_ (σ := .w) (.lit 95) (.cmp .eq (.s (.s .z)) .z)))) (.ite .z (.call ⟨26, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.blit false))) .nil))))
def b27 : Proven.S3.Expr S [(.d 0)] (.d 5) :=
  (.cas (i := 0) .z (Alts.arms (.cons (.mk 5 0 .nil) (.cons (.let_ (σ := (.d 5)) (.call ⟨27, by decide⟩ (.cons (.s .z) .nil) rfl) (.let_ (σ := (.d 5)) (.let_ (σ := (.d 5)) (.mk 5 0 .nil) (.mk 5 1 (.cons .z .nil))) (.call ⟨28, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl))) .nil))))
def b28 : Proven.S3.Expr S [(.d 5), (.d 5)] (.d 5) :=
  (.cas (i := 5) (.s .z) (Alts.arms (.cons (.var .z) (.cons (.let_ (σ := (.d 5)) (.call ⟨28, by decide⟩ (.cons (.s .z) (.cons .z .nil)) rfl) (.mk 5 1 (.cons .z .nil))) .nil))))
def b29 : Proven.S3.Expr S [(.d 9), (.d 3)] (.d 1) :=
  (.cas (i := 9) .z (Alts.arms (.cons (.mk 1 0 .nil) (.cons (.let_ (σ := (.d 2)) (.mk 2 0 (.cons .z (.cons (.s (.s .z)) .nil))) (.mk 1 1 (.cons .z .nil))) .nil))))
def b30 : Proven.S3.Expr S [.w] (.d 9) :=
  (.let_ (σ := .b) (.let_ (σ := .w) (.lit 1) (.cmp .eq (.s .z) .z)) (.ite .z (.let_ (σ := .b) (.blit false) (.mk 9 1 (.cons .z .nil))) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 2) (.cmp .eq (.s (.s .z)) .z)) (.ite .z (.let_ (σ := .b) (.blit true) (.mk 9 1 (.cons .z .nil))) (.mk 9 0 .nil)))))
def b31 : Proven.S3.Expr S [.w, (.d 3)] .w :=
  (.cas (i := 3) (.s .z) (Alts.arms (.cons (.var .z) (.cons (.let_ (σ := .b) (.let_ (σ := .w) (.call ⟨32, by decide⟩ (.cons .z .nil) rfl) (.let_ (σ := .w) (.lit 0) (.cmp .eq (.s .z) .z))) (.ite .z (.call ⟨31, by decide⟩ (.cons (.s (.s (.s .z))) (.cons (.s (.s .z)) .nil)) rfl) (.let_ (σ := .b) (.let_ (σ := .w) (.lit 0) (.cmp .eq (.s (.s (.s (.s .z)))) .z)) (.ite .z (.let_ (σ := .w) (.call ⟨32, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.call ⟨31, by decide⟩ (.cons .z (.cons (.s (.s (.s (.s .z)))) .nil)) rfl)) (.let_ (σ := .b) (.let_ (σ := .w) (.call ⟨32, by decide⟩ (.cons (.s (.s .z)) .nil) rfl) (.cmp .eq (.s (.s (.s (.s (.s .z))))) .z)) (.ite .z (.call ⟨31, by decide⟩ (.cons (.s (.s (.s (.s (.s .z))))) (.cons (.s (.s (.s (.s .z)))) .nil)) rfl) (.lit 3))))))) .nil))))
def b32 : Proven.S3.Expr S [(.d 4)] .w :=
  (.cas (i := 4) .z (Alts.arms (.cons (.lit 0) (.cons (.lit 0) (.cons (.let_ (σ := .b) (.var .z) (.ite .z (.lit 2) (.lit 1))) (.cons (.lit 0) (.cons (.lit 0) (.cons (.lit 0) (.cons (.lit 0) (.cons (.lit 0) (.cons (.lit 0) (.cons (.lit 0) (.cons (.lit 0) (.cons (.lit 0) (.cons (.lit 0) .nil)))))))))))))))
abbrev P : Proven.S3.Prog := ⟨S, (.cons b0 (.cons b1 (.cons b2 (.cons b3 (.cons b4 (.cons b5 (.cons b6 (.cons b7 (.cons b8 (.cons b9 (.cons b10 (.cons b11 (.cons b12 (.cons b13 (.cons b14 (.cons b15 (.cons b16 (.cons b17 (.cons b18 (.cons b19 (.cons b20 (.cons b21 (.cons b22 (.cons b23 (.cons b24 (.cons b25 (.cons b26 (.cons b27 (.cons b28 (.cons b29 (.cons b30 (.cons b31 (.cons b32 .nil))))))))))))))))))))))))))))))))), ⟨0, by decide⟩⟩
def φ : Fin P.S.fns.length → List Proven.S3.V → Proven.S3.V := fun f vs => match f.val with
  | 0 => Proven.S3.Enc.enc ((Nano.LS.lexA) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 1 => Proven.S3.Enc.enc ((Nano.PS.encT) (Proven.S3.Enc.dec (vs.getD 0 default) : (Option (Prod Bool (List Nano.Tok)))))
  | 2 => Proven.S3.Enc.enc ((Nano.PS.encToks) (Proven.S3.Enc.dec (vs.getD 0 default) : (List Nano.Tok)))
  | 3 => Proven.S3.Enc.enc ((@List.append UInt8) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)) (Proven.S3.Enc.dec (vs.getD 1 default) : (List UInt8)))
  | 4 => Proven.S3.Enc.enc ((Nano.PS.encTok) (Proven.S3.Enc.dec (vs.getD 0 default) : (Nano.Tok)))
  | 5 => Proven.S3.Enc.enc ((Nano.PS.encId) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 6 => Proven.S3.Enc.enc ((Nano.PS.le8) (Proven.S3.Enc.dec (vs.getD 0 default) : (UInt64)))
  | 7 => Proven.S3.Enc.enc ((Nano.LS.lexTS) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 8 => Proven.S3.Enc.enc ((Nano.adjOk) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 9 => Proven.S3.Enc.enc ((Nano.isWordC) (Proven.S3.Enc.dec (vs.getD 0 default) : (UInt8)))
  | 10 => Proven.S3.Enc.enc ((Nano.isLetter) (Proven.S3.Enc.dec (vs.getD 0 default) : (UInt8)))
  | 11 => Proven.S3.Enc.enc ((Nano.isDigit) (Proven.S3.Enc.dec (vs.getD 0 default) : (UInt8)))
  | 12 => Proven.S3.Enc.enc ((Nano.LS.lexS) (Proven.S3.Enc.dec (vs.getD 0 default) : (Nat)) (Proven.S3.Enc.dec (vs.getD 1 default) : (List UInt8)))
  | 13 => Proven.S3.Enc.enc ((Nano.LS.nextW) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 14 => Proven.S3.Enc.enc ((Nano.PS.consO) (Proven.S3.Enc.dec (vs.getD 0 default) : (Nano.Tok)) (Proven.S3.Enc.dec (vs.getD 1 default) : (Option (List Nano.Tok))))
  | 15 => Proven.S3.Enc.enc ((Nano.LS.spanS) (Proven.S3.Enc.dec (vs.getD 0 default) : (Nat)) (Proven.S3.Enc.dec (vs.getD 1 default) : (List UInt8)))
  | 16 => Proven.S3.Enc.enc ((Nano.LS.consP) (Proven.S3.Enc.dec (vs.getD 0 default) : (UInt8)) (Proven.S3.Enc.dec (vs.getD 1 default) : (Prod (List UInt8) (List UInt8))))
  | 17 => Proven.S3.Enc.enc ((Nano.LS.wordTokS) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 18 => Proven.S3.Enc.enc ((Nano.LS.allDig) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 19 => Proven.S3.Enc.enc ((Nano.LS.numW) (Proven.S3.Enc.dec (vs.getD 0 default) : (UInt64)) (Proven.S3.Enc.dec (vs.getD 1 default) : (List UInt8)))
  | 20 => Proven.S3.Enc.enc ((Nano.LS.isDef) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 21 => Proven.S3.Enc.enc ((@List.isEmpty UInt8) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 22 => Proven.S3.Enc.enc ((Nano.LS.isLet) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 23 => Proven.S3.Enc.enc ((Nano.LS.isU64) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 24 => Proven.S3.Enc.enc ((Nano.LS.isI64) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 25 => Proven.S3.Enc.enc ((Nano.LS.identOkS) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 26 => Proven.S3.Enc.enc ((Nano.LS.allDU) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 27 => Proven.S3.Enc.enc ((@List.length UInt8) (Proven.S3.Enc.dec (vs.getD 0 default) : (List UInt8)))
  | 28 => Proven.S3.Enc.enc ((Nat.add) (Proven.S3.Enc.dec (vs.getD 0 default) : (Nat)) (Proven.S3.Enc.dec (vs.getD 1 default) : (Nat)))
  | 29 => Proven.S3.Enc.enc ((Nano.LS.pairT) (Proven.S3.Enc.dec (vs.getD 0 default) : (Option Bool)) (Proven.S3.Enc.dec (vs.getD 1 default) : (List Nano.Tok)))
  | 30 => Proven.S3.Enc.enc ((Nano.LS.decT) (Proven.S3.Enc.dec (vs.getD 0 default) : (UInt64)))
  | 31 => Proven.S3.Enc.enc ((Nano.LS.uniW) (Proven.S3.Enc.dec (vs.getD 0 default) : (UInt64)) (Proven.S3.Enc.dec (vs.getD 1 default) : (List Nano.Tok)))
  | 32 => Proven.S3.Enc.enc ((Nano.LS.tyCode) (Proven.S3.Enc.dec (vs.getD 0 default) : (Nano.Tok)))
  | _ => default
theorem body3 : P.body ⟨3, by decide⟩ = b3 := rfl
theorem phi3 : ∀ (x0 : (List UInt8)) (x1 : (List UInt8)), φ ⟨3, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] = Proven.S3.Enc.enc ((@List.append UInt8) x0 x1) := by
  intro x0 x1
  simp [φ]
theorem cert3 : ∀ (x0 : (List UInt8)) (x1 : (List UInt8)), Proven.S3.Good P φ ⟨3, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] := by
  sorry
theorem cert3' : ∀ v0 v1 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Enc.enc (Proven.S3.Enc.dec v1 : (List UInt8)) = v1 → Proven.S3.Good P φ ⟨3, by decide⟩ [v0, v1] := by
  intro v0 v1 h0 h1
  have := cert3 (Proven.S3.Enc.dec v0) (Proven.S3.Enc.dec v1)
  rw [h0, h1] at this
  exact this
theorem body5 : P.body ⟨5, by decide⟩ = b5 := rfl
theorem phi5 : ∀ (x0 : (List UInt8)), φ ⟨5, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.PS.encId) x0) := by
  intro x0
  simp [φ]
theorem cert5 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨5, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert5' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨5, by decide⟩ [v0] := by
  intro v0 h0
  have := cert5 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body6 : P.body ⟨6, by decide⟩ = b6 := rfl
theorem phi6 : ∀ (x0 : (UInt64)), φ ⟨6, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.PS.le8) x0) := by
  intro x0
  simp [φ]
theorem cert6 : ∀ (x0 : (UInt64)), Proven.S3.Good P φ ⟨6, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert6' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (UInt64)) = v0 → Proven.S3.Good P φ ⟨6, by decide⟩ [v0] := by
  intro v0 h0
  have := cert6 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body10 : P.body ⟨10, by decide⟩ = b10 := rfl
theorem phi10 : ∀ (x0 : (UInt8)), φ ⟨10, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.isLetter) x0) := by
  intro x0
  simp [φ]
theorem cert10 : ∀ (x0 : (UInt8)), Proven.S3.Good P φ ⟨10, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert10' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (UInt8)) = v0 → Proven.S3.Good P φ ⟨10, by decide⟩ [v0] := by
  intro v0 h0
  have := cert10 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body11 : P.body ⟨11, by decide⟩ = b11 := rfl
theorem phi11 : ∀ (x0 : (UInt8)), φ ⟨11, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.isDigit) x0) := by
  intro x0
  simp [φ]
theorem cert11 : ∀ (x0 : (UInt8)), Proven.S3.Good P φ ⟨11, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert11' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (UInt8)) = v0 → Proven.S3.Good P φ ⟨11, by decide⟩ [v0] := by
  intro v0 h0
  have := cert11 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body14 : P.body ⟨14, by decide⟩ = b14 := rfl
theorem phi14 : ∀ (x0 : (Nano.Tok)) (x1 : (Option (List Nano.Tok))), φ ⟨14, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] = Proven.S3.Enc.enc ((Nano.PS.consO) x0 x1) := by
  intro x0 x1
  simp [φ]
theorem cert14 : ∀ (x0 : (Nano.Tok)) (x1 : (Option (List Nano.Tok))), Proven.S3.Good P φ ⟨14, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] := by
  sorry
theorem cert14' : ∀ v0 v1 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (Nano.Tok)) = v0 → Proven.S3.Enc.enc (Proven.S3.Enc.dec v1 : (Option (List Nano.Tok))) = v1 → Proven.S3.Good P φ ⟨14, by decide⟩ [v0, v1] := by
  intro v0 v1 h0 h1
  have := cert14 (Proven.S3.Enc.dec v0) (Proven.S3.Enc.dec v1)
  rw [h0, h1] at this
  exact this
theorem body16 : P.body ⟨16, by decide⟩ = b16 := rfl
theorem phi16 : ∀ (x0 : (UInt8)) (x1 : (Prod (List UInt8) (List UInt8))), φ ⟨16, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] = Proven.S3.Enc.enc ((Nano.LS.consP) x0 x1) := by
  intro x0 x1
  simp [φ]
theorem cert16 : ∀ (x0 : (UInt8)) (x1 : (Prod (List UInt8) (List UInt8))), Proven.S3.Good P φ ⟨16, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] := by
  sorry
theorem cert16' : ∀ v0 v1 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (UInt8)) = v0 → Proven.S3.Enc.enc (Proven.S3.Enc.dec v1 : (Prod (List UInt8) (List UInt8))) = v1 → Proven.S3.Good P φ ⟨16, by decide⟩ [v0, v1] := by
  intro v0 v1 h0 h1
  have := cert16 (Proven.S3.Enc.dec v0) (Proven.S3.Enc.dec v1)
  rw [h0, h1] at this
  exact this
theorem body18 : P.body ⟨18, by decide⟩ = b18 := rfl
theorem phi18 : ∀ (x0 : (List UInt8)), φ ⟨18, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.allDig) x0) := by
  intro x0
  simp [φ]
theorem cert18 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨18, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert18' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨18, by decide⟩ [v0] := by
  intro v0 h0
  have := cert18 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body19 : P.body ⟨19, by decide⟩ = b19 := rfl
theorem phi19 : ∀ (x0 : (UInt64)) (x1 : (List UInt8)), φ ⟨19, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] = Proven.S3.Enc.enc ((Nano.LS.numW) x0 x1) := by
  intro x0 x1
  simp [φ]
theorem cert19 : ∀ (x0 : (UInt64)) (x1 : (List UInt8)), Proven.S3.Good P φ ⟨19, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] := by
  sorry
theorem cert19' : ∀ v0 v1 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (UInt64)) = v0 → Proven.S3.Enc.enc (Proven.S3.Enc.dec v1 : (List UInt8)) = v1 → Proven.S3.Good P φ ⟨19, by decide⟩ [v0, v1] := by
  intro v0 v1 h0 h1
  have := cert19 (Proven.S3.Enc.dec v0) (Proven.S3.Enc.dec v1)
  rw [h0, h1] at this
  exact this
theorem body21 : P.body ⟨21, by decide⟩ = b21 := rfl
theorem phi21 : ∀ (x0 : (List UInt8)), φ ⟨21, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((@List.isEmpty UInt8) x0) := by
  intro x0
  simp [φ]
theorem cert21 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨21, by decide⟩ [Proven.S3.Enc.enc x0] := by
  intro x0
  (
  (apply Proven.S3.good_intro <;> rw [body21]) <;> (try rw [phi21]) <;> (try rw [List.isEmpty.eq_def]) <;>
  s3_solveF 12 [Proven.S3.evalO, Proven.S3.CallsOk, Proven.S3.Var.idx, Proven.S3.Alts.arms, Proven.S3.Vars.get, Proven.S3.Vars.idxs, Proven.S3.Prim.eval, Proven.Op.eval, Proven.S3.Cmp.eval, Proven.S3.Sig.nc, Proven.S3.Sig.fld, Proven.S3.Sig.dt, Proven.S3.lget, -Fin.isValue, -UInt8.ofNat_uInt64ToNat, b21, φ, *] with (first | assumption | (intros; assumption) | omega))
theorem cert21' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨21, by decide⟩ [v0] := by
  intro v0 h0
  have := cert21 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body22 : P.body ⟨22, by decide⟩ = b22 := rfl
theorem phi22 : ∀ (x0 : (List UInt8)), φ ⟨22, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.isLet) x0) := by
  intro x0
  simp [φ]
theorem cert22 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨22, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert22' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨22, by decide⟩ [v0] := by
  intro v0 h0
  have := cert22 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body23 : P.body ⟨23, by decide⟩ = b23 := rfl
theorem phi23 : ∀ (x0 : (List UInt8)), φ ⟨23, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.isU64) x0) := by
  intro x0
  simp [φ]
theorem cert23 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨23, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert23' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨23, by decide⟩ [v0] := by
  intro v0 h0
  have := cert23 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body24 : P.body ⟨24, by decide⟩ = b24 := rfl
theorem phi24 : ∀ (x0 : (List UInt8)), φ ⟨24, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.isI64) x0) := by
  intro x0
  simp [φ]
theorem cert24 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨24, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert24' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨24, by decide⟩ [v0] := by
  intro v0 h0
  have := cert24 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body26 : P.body ⟨26, by decide⟩ = b26 := rfl
theorem phi26 : ∀ (x0 : (List UInt8)), φ ⟨26, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.allDU) x0) := by
  intro x0
  simp [φ]
theorem cert26 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨26, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert26' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨26, by decide⟩ [v0] := by
  intro v0 h0
  have := cert26 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body28 : P.body ⟨28, by decide⟩ = b28 := rfl
theorem phi28 : ∀ (x0 : (Nat)) (x1 : (Nat)), φ ⟨28, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] = Proven.S3.Enc.enc ((Nat.add) x0 x1) := by
  intro x0 x1
  simp [φ]
theorem cert28 : ∀ (x0 : (Nat)) (x1 : (Nat)), Proven.S3.Good P φ ⟨28, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] := by
  sorry
theorem cert28' : ∀ v0 v1 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (Nat)) = v0 → Proven.S3.Enc.enc (Proven.S3.Enc.dec v1 : (Nat)) = v1 → Proven.S3.Good P φ ⟨28, by decide⟩ [v0, v1] := by
  intro v0 v1 h0 h1
  have := cert28 (Proven.S3.Enc.dec v0) (Proven.S3.Enc.dec v1)
  rw [h0, h1] at this
  exact this
theorem body29 : P.body ⟨29, by decide⟩ = b29 := rfl
theorem phi29 : ∀ (x0 : (Option Bool)) (x1 : (List Nano.Tok)), φ ⟨29, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] = Proven.S3.Enc.enc ((Nano.LS.pairT) x0 x1) := by
  intro x0 x1
  simp [φ]
theorem cert29 : ∀ (x0 : (Option Bool)) (x1 : (List Nano.Tok)), Proven.S3.Good P φ ⟨29, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] := by
  sorry
theorem cert29' : ∀ v0 v1 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (Option Bool)) = v0 → Proven.S3.Enc.enc (Proven.S3.Enc.dec v1 : (List Nano.Tok)) = v1 → Proven.S3.Good P φ ⟨29, by decide⟩ [v0, v1] := by
  intro v0 v1 h0 h1
  have := cert29 (Proven.S3.Enc.dec v0) (Proven.S3.Enc.dec v1)
  rw [h0, h1] at this
  exact this
theorem body30 : P.body ⟨30, by decide⟩ = b30 := rfl
theorem phi30 : ∀ (x0 : (UInt64)), φ ⟨30, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.decT) x0) := by
  intro x0
  simp [φ]
theorem cert30 : ∀ (x0 : (UInt64)), Proven.S3.Good P φ ⟨30, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert30' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (UInt64)) = v0 → Proven.S3.Good P φ ⟨30, by decide⟩ [v0] := by
  intro v0 h0
  have := cert30 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body32 : P.body ⟨32, by decide⟩ = b32 := rfl
theorem phi32 : ∀ (x0 : (Nano.Tok)), φ ⟨32, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.tyCode) x0) := by
  intro x0
  simp [φ]
theorem cert32 : ∀ (x0 : (Nano.Tok)), Proven.S3.Good P φ ⟨32, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert32' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (Nano.Tok)) = v0 → Proven.S3.Good P φ ⟨32, by decide⟩ [v0] := by
  intro v0 h0
  have := cert32 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body4 : P.body ⟨4, by decide⟩ = b4 := rfl
theorem phi4 : ∀ (x0 : (Nano.Tok)), φ ⟨4, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.PS.encTok) x0) := by
  intro x0
  simp [φ]
theorem cert4 : ∀ (x0 : (Nano.Tok)), Proven.S3.Good P φ ⟨4, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert4' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (Nano.Tok)) = v0 → Proven.S3.Good P φ ⟨4, by decide⟩ [v0] := by
  intro v0 h0
  have := cert4 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body9 : P.body ⟨9, by decide⟩ = b9 := rfl
theorem phi9 : ∀ (x0 : (UInt8)), φ ⟨9, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.isWordC) x0) := by
  intro x0
  simp [φ]
theorem cert9 : ∀ (x0 : (UInt8)), Proven.S3.Good P φ ⟨9, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert9' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (UInt8)) = v0 → Proven.S3.Good P φ ⟨9, by decide⟩ [v0] := by
  intro v0 h0
  have := cert9 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body13 : P.body ⟨13, by decide⟩ = b13 := rfl
theorem phi13 : ∀ (x0 : (List UInt8)), φ ⟨13, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.nextW) x0) := by
  intro x0
  simp [φ]
theorem cert13 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨13, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert13' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨13, by decide⟩ [v0] := by
  intro v0 h0
  have := cert13 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body15 : P.body ⟨15, by decide⟩ = b15 := rfl
theorem phi15 : ∀ (x0 : (Nat)) (x1 : (List UInt8)), φ ⟨15, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] = Proven.S3.Enc.enc ((Nano.LS.spanS) x0 x1) := by
  intro x0 x1
  simp [φ]
theorem cert15 : ∀ (x0 : (Nat)) (x1 : (List UInt8)), Proven.S3.Good P φ ⟨15, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] := by
  sorry
theorem cert15' : ∀ v0 v1 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (Nat)) = v0 → Proven.S3.Enc.enc (Proven.S3.Enc.dec v1 : (List UInt8)) = v1 → Proven.S3.Good P φ ⟨15, by decide⟩ [v0, v1] := by
  intro v0 v1 h0 h1
  have := cert15 (Proven.S3.Enc.dec v0) (Proven.S3.Enc.dec v1)
  rw [h0, h1] at this
  exact this
theorem body20 : P.body ⟨20, by decide⟩ = b20 := rfl
theorem phi20 : ∀ (x0 : (List UInt8)), φ ⟨20, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.isDef) x0) := by
  intro x0
  simp [φ]
theorem cert20 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨20, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert20' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨20, by decide⟩ [v0] := by
  intro v0 h0
  have := cert20 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body25 : P.body ⟨25, by decide⟩ = b25 := rfl
theorem phi25 : ∀ (x0 : (List UInt8)), φ ⟨25, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.identOkS) x0) := by
  intro x0
  simp [φ]
theorem cert25 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨25, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert25' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨25, by decide⟩ [v0] := by
  intro v0 h0
  have := cert25 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body27 : P.body ⟨27, by decide⟩ = b27 := rfl
theorem phi27 : ∀ (x0 : (List UInt8)), φ ⟨27, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((@List.length UInt8) x0) := by
  intro x0
  simp [φ]
theorem cert27 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨27, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert27' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨27, by decide⟩ [v0] := by
  intro v0 h0
  have := cert27 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body31 : P.body ⟨31, by decide⟩ = b31 := rfl
theorem phi31 : ∀ (x0 : (UInt64)) (x1 : (List Nano.Tok)), φ ⟨31, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] = Proven.S3.Enc.enc ((Nano.LS.uniW) x0 x1) := by
  intro x0 x1
  simp [φ]
theorem cert31 : ∀ (x0 : (UInt64)) (x1 : (List Nano.Tok)), Proven.S3.Good P φ ⟨31, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] := by
  sorry
theorem cert31' : ∀ v0 v1 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (UInt64)) = v0 → Proven.S3.Enc.enc (Proven.S3.Enc.dec v1 : (List Nano.Tok)) = v1 → Proven.S3.Good P φ ⟨31, by decide⟩ [v0, v1] := by
  intro v0 v1 h0 h1
  have := cert31 (Proven.S3.Enc.dec v0) (Proven.S3.Enc.dec v1)
  rw [h0, h1] at this
  exact this
theorem body2 : P.body ⟨2, by decide⟩ = b2 := rfl
theorem phi2 : ∀ (x0 : (List Nano.Tok)), φ ⟨2, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.PS.encToks) x0) := by
  intro x0
  simp [φ]
theorem cert2 : ∀ (x0 : (List Nano.Tok)), Proven.S3.Good P φ ⟨2, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert2' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List Nano.Tok)) = v0 → Proven.S3.Good P φ ⟨2, by decide⟩ [v0] := by
  intro v0 h0
  have := cert2 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body8 : P.body ⟨8, by decide⟩ = b8 := rfl
theorem phi8 : ∀ (x0 : (List UInt8)), φ ⟨8, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.adjOk) x0) := by
  intro x0
  simp [φ]
theorem cert8 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨8, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert8' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨8, by decide⟩ [v0] := by
  intro v0 h0
  have := cert8 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body17 : P.body ⟨17, by decide⟩ = b17 := rfl
theorem phi17 : ∀ (x0 : (List UInt8)), φ ⟨17, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.wordTokS) x0) := by
  intro x0
  simp [φ]
theorem cert17 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨17, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert17' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨17, by decide⟩ [v0] := by
  intro v0 h0
  have := cert17 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body1 : P.body ⟨1, by decide⟩ = b1 := rfl
theorem phi1 : ∀ (x0 : (Option (Prod Bool (List Nano.Tok)))), φ ⟨1, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.PS.encT) x0) := by
  intro x0
  simp [φ]
theorem cert1 : ∀ (x0 : (Option (Prod Bool (List Nano.Tok)))), Proven.S3.Good P φ ⟨1, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert1' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (Option (Prod Bool (List Nano.Tok)))) = v0 → Proven.S3.Good P φ ⟨1, by decide⟩ [v0] := by
  intro v0 h0
  have := cert1 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body12 : P.body ⟨12, by decide⟩ = b12 := rfl
theorem phi12 : ∀ (x0 : (Nat)) (x1 : (List UInt8)), φ ⟨12, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] = Proven.S3.Enc.enc ((Nano.LS.lexS) x0 x1) := by
  intro x0 x1
  simp [φ]
theorem cert12 : ∀ (x0 : (Nat)) (x1 : (List UInt8)), Proven.S3.Good P φ ⟨12, by decide⟩ [Proven.S3.Enc.enc x0, Proven.S3.Enc.enc x1] := by
  sorry
theorem cert12' : ∀ v0 v1 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (Nat)) = v0 → Proven.S3.Enc.enc (Proven.S3.Enc.dec v1 : (List UInt8)) = v1 → Proven.S3.Good P φ ⟨12, by decide⟩ [v0, v1] := by
  intro v0 v1 h0 h1
  have := cert12 (Proven.S3.Enc.dec v0) (Proven.S3.Enc.dec v1)
  rw [h0, h1] at this
  exact this
theorem body7 : P.body ⟨7, by decide⟩ = b7 := rfl
theorem phi7 : ∀ (x0 : (List UInt8)), φ ⟨7, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.lexTS) x0) := by
  intro x0
  simp [φ]
theorem cert7 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨7, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
theorem cert7' : ∀ v0 : Proven.S3.V, Proven.S3.Enc.enc (Proven.S3.Enc.dec v0 : (List UInt8)) = v0 → Proven.S3.Good P φ ⟨7, by decide⟩ [v0] := by
  intro v0 h0
  have := cert7 (Proven.S3.Enc.dec v0)
  rw [h0] at this
  exact this
theorem body0 : P.body ⟨0, by decide⟩ = b0 := rfl
theorem phi0 : ∀ (x0 : (List UInt8)), φ ⟨0, by decide⟩ [Proven.S3.Enc.enc x0] = Proven.S3.Enc.enc ((Nano.LS.lexA) x0) := by
  intro x0
  simp [φ]
theorem cert0 : ∀ (x0 : (List UInt8)), Proven.S3.Good P φ ⟨0, by decide⟩ [Proven.S3.Enc.enc x0] := by
  sorry
end LexA

end Nano.LS
