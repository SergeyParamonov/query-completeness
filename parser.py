#READ TODO below (search for it)
class atom:
  args = []
  predicate = ""
  def __init__(self, predicate, args):
    self.args = args
    self.predicate = predicate
  def get_predicate(self):
    return self.predicate
  def get_args(self):
    return self.args
  def __str__(self):
    return self.predicate + "(" + ",".join(self.args) + ")"
  def __repr__(self):
    return self.__str__()
  def get_a_version(self):
    return self.predicate + "_a" + "(" + ",".join(self.args) + ")"
  def get_i_version(self):
    return self.predicate + "_i" + "(" + ",".join(self.args) + ")"


class rule:
  head = "" #single atom
  body = "" #list of atoms
  def __init__(self, head, body):
    self.head = head
    self.body = body
  def get_head(self):
    return self.head
  def get_body(self):
    return self.body
  def __str__(self):
    out = str(self.head) + " :-" 
    prefix = " "
    flag = True
    for body_atom in self.body:
      out += prefix + str(body_atom)
      if flag:
        flag = False
        prefix = " AND "
    return out
  def __repr__(self):
    return self.__str__()


def parse_atom(txt):  
  txt = txt.strip()
  indx_bracket = txt.index("(")
  predicate   = txt[:indx_bracket]
  txt  = txt[indx_bracket+1:]
  args = txt.strip(")").split(",")
  return atom(predicate, args)

def parse_schema(lines):
  atoms = []
  for line in lines:
    head, body = line.strip().split(";")
    body       = body.split(",")
    schema_atom       = atom(head,body)
    atoms.append(schema_atom)
  return atoms
  
def parse_rule(line):
  head, body = line.split(";")
  head = parse_atom(head)
  body_atoms = body.strip().split("AND")
  body = []
  if body_atoms != ['']:
    for body_atom in body_atoms:
      body.append(parse_atom(body_atom))
  return rule(head,body)

def parse_query(lines):
  if len(lines) != 1:
    raise Exception("there is something wrong with the query syntax!")
  line = lines[0]
  return parse_rule(line)  

def parse_tc(lines):
  TCs = []
  for line in lines:
    TCs.append(parse_rule(line))
  return TCs

def parse_fk(lines):
  fks = []
  for line in lines:
    from_atom, to_atom = line.split(";")
    from_atom = parse_atom(from_atom) 
    to_atom   = parse_atom(to_atom)
    fks.append((from_atom,to_atom))
  return fks

def parse_fd(lines):
  fds = []
  for line in lines:
    fd_atom, indx, domain = line.split(";")
    fd_atom = parse_atom(fd_atom)
    indx    = int(indx)
    domain  = list(map(lambda x: x.strip(), domain.strip().split(",")))
    fds.append((fd_atom, indx,domain))
  return fds

def get_type(pred_name, position, schema):
  for schema_atom in schema:
    if schema_atom.get_predicate() == pred_name:
      return schema_atom.get_args()[position]

def get_expansion_types(fds, schema):
  types = set()
  for fd in fds:
    atm, indx, domain = fd
    expansion_type = get_type(atm.get_predicate(), indx-1, schema)
    types.add(expansion_type)
  return list(types)

structures = {}
def create_vocabulary(out_file):
  print("vocabulary V{", file=out_file)
  schema = structures["SCHEMA"]
  types = set()
  for atm in schema:
    for arg in atm.get_args():
      types.add(arg)
  for schema_type in types:
    print("type "+schema_type, file=out_file)
  
  for atm in schema:
    print(atm, file=out_file)
    print(atm.get_a_version(), file=out_file)
  
  query = structures["QUERY"]
  prefix = "frozen_"
  frozen_vars = query.get_head().get_args()
  frozen_set  = set()
  print("// frozen variables", file=out_file)
  for frozen in frozen_vars:
    for atm in query.get_body():
      args = atm.get_args()
      if frozen in args:
        frozen_type = get_type(atm.get_predicate(), atm.get_args().index(frozen), schema)
        frozen_set.add((frozen,frozen_type))
  for frozen,fr_type in frozen_set:
    print(frozen + ":" + fr_type, file=out_file)
  structures["FROZEN"] = frozen_set

  print("val predicates", file=out_file)
  fds = structures["FD"]
  for fd in fds:
    atm, indx, domain = fd
    var_type = get_type(atm.get_predicate(), indx-1, schema)   
    v_type = "v_" + var_type 
    prefix = "val_"
    print("type " + v_type, file=out_file)
    print(prefix + var_type +"(" + var_type + "," + v_type + ")", file=out_file)
  print("}")

def create_fd(fd, schema):
  atm, indx, domain = fd
  exp_type = get_type(atm.get_predicate(), indx-1, schema)

def isJoined(X, body):
  count = 0
  for atm in body:
    if X in atm.get_args():
      count += 1
  if count >= 2:
    return True
  else: 
    return False

def create_val(Xprime, X, val_type):
  return "val_"+val_type + "(" +Xprime+","+"v_"+X+")"


def create_theory(out_file):
  schema = structures["SCHEMA"]
  expansion_types = get_expansion_types(structures["FD"], schema)
  tcs = structures["TC"]
  print("theory T:V{", file=out_file)
  for tc in tcs:
    head = tc.get_head()
    body = tc.get_body()
    head_pred = head.get_predicate()
    all_tc_atoms = [head] + body
    vals = []
    fresh_vars = {}
    fresh_index = 1
    out_str = ""
    head_a = None
    for atm_indx, atm in enumerate(all_tc_atoms, start=1):
        vals = ""
        replace_index = [] # within the atom "atm"
        atm_vars = atm.get_args()
        for indx, arg in enumerate(atm_vars):
            predicate = atm.get_predicate()
            var_type = get_type(predicate, indx, schema)
            if var_type in expansion_types and isJoined(arg,all_tc_atoms):
                fresh_var = arg + "_fresh_" + str(fresh_index)
                fresh_vars[(atm_indx,indx)] = fresh_var
                replace_index.append(indx)
                fresh_index += 1
                vals += create_val(fresh_var, arg, var_type) + ","
        new_args = []
        for indx, var in enumerate(atm_vars):        
            if indx in replace_index:
                new_arg = fresh_vars[(atm_indx,indx)] 
            else:
                new_arg = atm_vars[indx]
            new_args.append(new_arg)
        fresh_atom = atom(predicate, new_args)
        if atm_indx == 1:
          head_a = atom(fresh_atom.get_predicate() + "_a", fresh_atom.get_args())
        out_str += str(fresh_atom) + "," + vals
    out_str = out_str.strip(",") + "."
    #TODO write copy head with fresh variables
    print(str(head_a) + " <- " + out_str)
    
  print("}", file=out_file)
    

parse_functions = {"SCHEMA": parse_schema, "QUERY":parse_query, "TC":parse_tc, "FK":parse_fk, "FD":parse_fd, "SCHEMA":parse_schema}
keywords        = parse_functions.keys()
end_keyword     = "END"
input_file      = "input.txt"
data            = open(input_file, "r").read().splitlines()
parse_function  = None
lines = []
for raw_line in data:
  line = raw_line.strip()
  if line in keywords: 
    keyword = line
    parse_function = parse_functions[keyword]
    lines = []
  elif line == end_keyword:
    structures[keyword] = parse_function(lines)
  else:
    lines.append(line)

#print(structures["SCHEMA"])
#print(structures["QUERY"])
print(structures["TC"])
print(structures["FD"])
#print(structures["FK"])
from sys import stdout
#create_vocabulary(stdout)
create_theory(stdout)
