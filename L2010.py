from z3 import *

sent_letters = 'PQRSTUVWXYZ'
functions = 'abcdefgh'
variables = 'ijklmnopqrstuvwxyz'
mono_preds = 'ABCDEFGHIJKLMNO'
poly_preds = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
connectives = '∧∨→↔'
quantifiers = '∀∃'

def rm_spaces(s):
  return s.replace(' ','')

def rm_neq(s) :
  if not ('≠' in s) :
    return s
  elif breaks(s, [is_any, is_term, is_neq, is_any]) :
    t = breaks(s, [is_any, is_term, is_neq, is_any]) 
    return rm_neq(t[0] + '~' + t[1] + '=' + t[3])
  else:
    return s

def is_any(s):
  return True

def is_eq(s):
  return s == '='

def is_neq(s):
  return s == '≠'

def is_neg(s):
  return s == '∼'

def is_lp(s):
  return s == '('

def is_rp(s):
  return s == ')'

def is_letter_in(s,list):
  return len(s) == 1 and s in list

def is_sent_letter(s): 
  return is_letter_in(s,sent_letters)

def is_func(s): 
  return is_letter_in(s,functions)

def is_var(s): 
  return is_letter_in(s,variables)

def is_mono_pred(s): 
  return is_letter_in(s,mono_preds)

def is_poly_pred(s):
  return is_letter_in(s,poly_preds)

def is_connective(s):
  return is_letter_in(s,connectives)

def is_quantifier(s):
  return is_letter_in(s,quantifiers)

def breaks(s,cl):
  if not cl:
    return []
  for i in range(0,len(s)+1):
    if cl[0](s[:i]):
      if breaks(s[i:],cl[1:]) or not (s[i:] or cl[1:]):
        return [s[:i]] + breaks(s[i:],cl[1:])
  return []

def is_term(s):
  return is_var(s) or is_func(s) or is_ap_func(s)

def is_ap_func(s):
  return breaks(s, [is_func, is_lp, is_term_concat, is_rp]) 

def is_term_concat(s) :
  if is_term(s) :
    return [s]
  elif breaks(s, [is_term, is_term_concat]) :
    p = breaks(s, [is_term, is_term_concat])
    return [p[0]] + is_term_concat(p[1])
  else :
    return []

def is_negation(s): 
  return breaks(s, [is_neg, is_formula]) 

def is_ap_mono_pred(s) :
  return breaks(s, [is_mono_pred, is_term]) 

def is_ap_poly_pred(s) :
  return breaks(s, [is_poly_pred, is_lp, is_term_concat, is_rp]) 

def is_formula(s): 
  return is_atom(s) or is_molecule(s)

def is_atom(s): 
  return is_sent_letter(s) or is_id(s) or is_ap_mono_pred(s) or is_ap_poly_pred(s) 

def is_id(s) : 
  return breaks(s, [is_term, is_eq, is_term]) 

def is_molecule(s): 
  return is_negation(s) or is_binary(s) or is_quantified(s)

def is_binary(s): 
  return breaks(s, [is_lp, is_formula, is_connective, is_formula, is_rp]) 

def is_quantified(s): 
  return breaks(s, [is_quantifier, is_var, is_formula]) 
 
def conv_formula(s0) :
  s = rm_spaces(s0)
  if is_atom(s) :
    return conv_atom(s)
  elif is_molecule(s) :
    return conv_molecule(s)
  else:
    return 'Error : not a wff'

def conv_atom(s):
  if is_sent_letter(s):
    return s
  elif is_id(s):
    return conv_id(s)
  elif is_ap_mono_pred(s):
    return conv_ap_mono_pred(s)
  elif is_ap_poly_pred(s):
    return conv_ap_poly_pred(s)
  else :
    return 'Error : not an atomic formula'

def conv_molecule(s) :
  if is_negation(s) :
    return conv_negation(s)
  elif is_binary(s) : 
    return conv_binary(s)
  elif is_quantified(s) :
    return conv_quantified(s)
  else :
    return 'Error : not a molecular formula'

def conv_negation(s) :
  return set_list(['not', conv_formula(is_negation(s)[1])])  

def conv_binary(s) :
  t = is_binary(s)
  return set_list([conv_connective(t[2]), conv_formula(t[1]), conv_formula(t[3])])  

def conv_quantified(s) :
  t = is_quantified(s)
  return set_list([conv_quantifer(t[0]), '((' + t[1] + ' U))', conv_formula(t[2])])  

def conv_quantifer(s) :
  if s == '∀' :
    return 'forall' 
  elif s == '∃' :
    return 'exists' 
  else : 
    return 'Error : not a quantifier' 

def conv_connective(s) :
  if s == '∧' :
    return 'and' 
  elif s == '∨' :
    return 'or' 
  elif s == '→' :
    return '=>' 
  elif s == '↔' :
    return '=' 
  else : 
    return 'Error : not a binary connective' 

def conv_id(s):
  t = is_id(s)
  return set_list(['=', conv_term(t[0]), conv_term(t[2])])  

def conv_ap_mono_pred(s) :
  p = is_ap_mono_pred(s)
  return set_list([p[0], conv_term(p[1])])

def conv_ap_poly_pred(s) :
  p = is_ap_poly_pred(s)
  c = is_term_concat(p[2])
  return set_list([p[0]] + [conv_term(x) for x in c])

def set_list(l) :
  return parens(list_to_string(l)) 

def parens(s):
  return '(' + s[1:] + ')'

def list_to_string(l):
  if not l:
    return ''
  else:
    return ' ' + l[0] + list_to_string(l[1:])

def conv_term(s) :
  if is_var(s) or is_func(s) :
    return s
  if is_ap_func(s) :
    return conv_ap_func(s)

def conv_ap_func(s) :
  p = is_ap_func(s)
  c = is_term_concat(p[2])
  return set_list([p[0]] + [conv_term(x) for x in c])

print(conv_formula('(Hy ∧ ∃z (Gz ∧ S(xyz)))'))

