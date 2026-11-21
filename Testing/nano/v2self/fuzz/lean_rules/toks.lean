import Lean
def isIdLike (s : String) : Bool := s.length > 0 && ((s.get 0).isAlpha || s.startsWith "_")
#eval show Lean.CoreM Unit from do
  let env ← Lean.getEnv
  let t := (Lean.Parser.parserExtension.getState env).tokens
  let ks := Lean.Data.Trie.values t
  let ks := (Array.filter (fun s => isIdLike s && s.all fun c => c.isAlphanum || c == '_' || c == '\'' || c=='!' || c=='?') ks)
  let ks := Array.qsort ks (· < ·)
  IO.FS.writeFile "/tmp/claude-0/lr/h/kw.txt" ("\n".intercalate (Array.toList ks))
