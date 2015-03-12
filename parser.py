class atom:
  args = []
  predicate = ""
  def __init__(self, predicate, args):
    self.args = args
    self.predicate = predicate
  def get_predicate():
    return self.predicate
  def get_args():
    return self.args
  def __str__(self):
    return self.predicate + "(" + ",".join(self.args) + ")"
  def __repr__(self):
    return self.__str__()

class rule:
  head = "" #single atom
  body = "" #list of atoms
  def __init__(self, head, body):
    self.head = head
    self.body = body
  def get_head():
    return self.head
  def get_body():
    return self.body
  def __str__(self):
    out = str(self.head) + ":-" 
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
    domain  = map(lambda x: x.strip(), domain.strip().split(","))
    fds.append((fd_atom, indx,domain))
  return fds

parse_functions = {"SCHEMA": parse_schema, "QUERY":parse_query, "TC":parse_tc, "FK":parse_fk, "FD":parse_fd, "SCHEMA":parse_schema}
structures = {}
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

print(structures["SCHEMA"])
print(structures["QUERY"])
print(structures["TC"])
print(structures["FK"])
print(structures["FD"])
