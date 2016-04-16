import pdb
from z3 import *

sent_letters = 'PQRSTUVWXYZ'
functions = 'abcdefgh'
variables = 'ijklmnopqrstuvwxyz'
mono_preds = 'ABCDEFGHIJKLMNO'
poly_preds = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
connectives = '∧∨→↔'
quantifiers = '∀∃'

def is_letter_in(s,list):
  return len(s) == 1 and s in list

def is_sent_letter(s): 
  return is_letter_in(s,sent_letters)

def is_func(s): 
  return is_letter_in(s,functions)

def is_var(s): 
  return is_letter_in(s,variables)

def is_neg(s):
  return s == '∼'

def is_connective(s):
  return is_letter_in(s,connectives)

def is_quantifier(s):
  return is_letter_in(s,quantifiers)

def conv_formula(s0) :
  s = rm_spaces(s0)
  if mc_at(s) == len(s) :
    return conv_atom(s) 
  else :
    return conv_molecule(s)

def rm_spaces(s) :
  return s.replace(' ','')

def mc_at(s) : # Returns the position of main connective. If atomic, returns len(s)
  if is_neg(s[0]) or is_quantifier(s[0]) :
    return 0
  for i in range(2,len(s)-2) :
    if is_connective(s[i]) and is_balanced(s[1:i]) :
      return i
  return len(s)

def is_balanced(s) :
  return s.count('(') == s.count(')')  

def conv_atom(s):
  if is_sent_letter(s):
    return s
  elif '=' in s:
    return conv_id(s)
  elif '≠' in s:
    return conv_nid(s)
  else :
    return conv_ap(paren_args(s))

def conv_molecule(s) :
  c = s[mc_at(s)] 
  if is_neg(c) :
    return conv_negation(s)
  elif is_connective(c) :
    return conv_binary(s)
  else : 
    return conv_quantified(s)

def conv_negation(s) :
  return set_list(['not', conv_formula(s[1:])])  

def conv_binary(s) :
  n = mc_at(s)
  return set_list([conv_connective(s[n]), conv_formula(s[1:n]), conv_formula(s[n+1:-1])])  

def conv_quantified(s) :
  return set_list([conv_quantifer(s[0]), '((' + s[1] + ' U))', conv_formula(s[2:])])  

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
  n = s.find('=')
  return set_list(['=', conv_term(s[0:n]), conv_term(s[n+1:])])  

def conv_nid(s):
  n = s.find('≠')
  return set_list(['not', set_list(['=', conv_term(s[0:n]), conv_term(s[n+1:])])])

def conv_ap(s) :
  l = parse_terms(s[2:-1])
  return set_list([s[0]] + [conv_term(x) for x in l])

def parse_terms(s) :
  if s == '' :
    return []
  elif len(s) == 1 :
    return [s]
  if s[1] != '(' :
    return [s[0]] + parse_terms(s[1:])
  else :
    return [s[:s.find(')')+1]] + parse_terms(s[s.find(')')+1:])

def paren_args(s) :
  if s[1] != '(' :
    return s[0] + '(' + s[1:] + ')'
  else :
    return s

def conv_term(s) :
  if is_var(s) or is_func(s) :
    return s
  else :
    return conv_ap(s)

def set_list(l) :
  return parens(list_to_string(l)) 

def parens(s):
  return '(' + s[1:] + ')'

def list_to_string(l):
  if not l:
    return ''
  else:
    return ' ' + l[0] + list_to_string(l[1:])

print(conv_formula('∀x (Gx → (∃y (Hy ∧ ∃z (Gz ∧ S(xyz))) → Fx))'))
