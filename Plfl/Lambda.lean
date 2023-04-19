-- https://plfa.github.io/Lambda/

def Sym : Type := String deriving Repr

inductive Term where
| var : Sym → Term
| lam : Sym → Term → Term
| ap : Term → Term → Term
| zero : Term
| succ : Term → Term
| case : Term → Term → Sym → Term → Term
| mu : Sym → Term → Term
deriving Repr

notation:50 " ƛ " v " ⇒ " d => Term.lam v d
notation:50 " μ " v " ⇒ " d => Term.mu v d
notation:max " ? " e " [zero⇒ " o " |succ " n " ⇒ " i " ] " => Term.case e o n i
infixr:70 " $ " => Term.ap
notation:max " ο " => Term.zero
prefix:80 " ι " => Term.succ
prefix:90 " ` " => Term.var

example : Term := `"foo"
example : Term := ? `"bar" [zero⇒ ο |succ "n" ⇒ ι ο]

namespace Term
  def one : Term := ι ο
  def two : Term := ι ι ο

  def add : Term := μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒ ? `"m" [zero⇒ `"n" |succ "m" ⇒ ι (`"+" $ `"m" $ `"n")]
  -- https://plfa.github.io/Lambda/#exercise-mul-recommended
  def mul : Term := μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒ ? `"m" [zero⇒ ο |succ "m" ⇒ `"+" $ `"n" $ `"*" $ `"m" $ `"n"]

  -- Church encoding...
  def one_c : Term := ƛ "s" ⇒ ƛ "z" ⇒ `"s" $ `"z"
  def two_c : Term := ƛ "s" ⇒ ƛ "z" ⇒ `"s" $ `"s" $ `"z"
  def suc_c : Term := ƛ "n" ⇒ ι `"n"
  def add_c : Term := ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ `"m" $ `"s" $ `"n" $ `"s" $ `"z"
  -- https://plfa.github.io/Lambda/#exercise-mul%E1%B6%9C-practice
  def mul_c : Term := ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ `"m" $ (`"n" $ `"s") $ `"z"
end Term
