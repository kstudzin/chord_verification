import random
from collections import defaultdict

NUM_BITS = 4
NUM_NODES = 3
MAX_ID = pow(2, NUM_BITS) - 1

random.seed(0)
node_ids = sorted(random.sample(range(0, MAX_ID), k=NUM_NODES))

next_node_p1 = """
    next(node{idx}.mode) := 
        case
    
            (node{idx}.mode = find_successor &
              (node{idx}.id >= node{idx}.successor_id | (node{idx}.id < n & n <= node{idx}.successor_id)) &
              (node{idx}.id <  node{idx}.successor_id | (n > node{idx}.id | n <= node{idx}.successor_id))) : 
                found_successor;
    
            (node{idx}.mode = find_successor & !(
              (node{idx}.id >= node{idx}.successor_id | (node{idx}.id < n & n <= node{idx}.successor_id)) &
              (node{idx}.id <  node{idx}.successor_id | (n > node{idx}.id | n <= node{idx}.successor_id)))) : 
                closest_preceding;\n\n"""

# node{idx}.mode = waiting & node2.mode = next_node & node2.index = 1 : find_successor ;
# node{idx}.mode = waiting & node3.mode = next_node & node3.index = 0 : find_successor ;

next_node_p2 = """
            node{idx}.mode = closest_preceding : get_next_finger ;

            node{idx}.mode = get_next_finger & node{idx}.index >= 0 : test_finger ;
            node{idx}.mode = get_next_finger & node{idx}.index < 0 : find_successor ;

            node{idx}.mode = test_finger &
              !(node{idx}.index >= 2 | node{idx}.index <= -1) &
              (node{idx}.id >= n | (node{idx}.id < fingers{idx}[node{idx}.index] & fingers{idx}[node{idx}.index] < n)) &
              (node{idx}.id <  n | (fingers{idx}[node{idx}.index] > node{idx}.id | fingers{idx}[node{idx}.index] < n)) : 
                next_node ;

            node{idx}.mode = test_finger &
              !(node{idx}.index >= 2 | node{idx}.index <= -1) &
              !((node{idx}.id >= n | (node{idx}.id < fingers{idx}[node{idx}.index] & fingers{idx}[node{idx}.index] < n)) &
              (node{idx}.id <  n | (fingers{idx}[node{idx}.index] > node{idx}.id | fingers{idx}[node{idx}.index] < n))) : 
                get_next_finger ;

            node{idx}.mode = next_node : waiting ;

            TRUE : node{idx}.mode ;
        esac;\n\n"""

smv = "MODULE main\n" \
      "\n" \
      "    FROZENVAR\n" \
      f"        n : 0..{MAX_ID};\n"

for i in range(0, NUM_NODES):
    smv = smv + f"        fingers{i} : array 0..{NUM_BITS - 1} of 0..{MAX_ID};\n"

smv = smv + "\n"
smv = smv + "    VAR\n"
for idx, node_id in enumerate(node_ids):
    next_idx = idx + 1 if idx < NUM_NODES - 1 else 0
    smv = smv + f"        node{idx} : node({node_id}, {node_ids[next_idx]}, fingers{idx});\n"

smv = smv + \
      "\n" \
      "    INIT\n"

for i in range(0, NUM_NODES):
    smv = smv + \
          "        ("
    for j in range(0, NUM_NODES):
        if i == j:
            smv = smv + f" node{j}.mode = find_successor "
        else:
            smv = smv + f" node{j}.mode = waiting "

        if j != NUM_NODES - 1:
            smv = smv + "&"

    smv = smv + ")"
    if i != NUM_NODES - 1:
        smv = smv + " |\n"
    else:
        smv = smv + ";\n"

smv = smv + \
      "\n" \
      "    ASSIGN\n"

fingers = defaultdict(set)
reverse_fingers = defaultdict(list)
for i in range(0, NUM_NODES):
    for j in range(0, NUM_BITS):
        finger = (node_ids[i] + pow(2, j)) % MAX_ID
        for k, node_id in enumerate(node_ids[i + 1:] + node_ids[:i + 1]):
            if finger < node_id:
                smv = smv + f"        init(fingers{i}[{j}]) := {node_id};\n"
                fingers[i].add((k + i + 1) % NUM_NODES)
                reverse_fingers[node_id].append((i, j))
                break
            if finger > node_ids[-1]:
                node_id = node_ids[0]
                smv = smv + f"        init(fingers{i}[{j}]) := {node_id};\n"
                fingers[i].add((k + i + 1) % NUM_NODES)
                reverse_fingers[node_id].append((i, j))
                break


for k, node_id in enumerate(node_ids):
    smv = smv + next_node_p1.format(idx=k)
    for i, j in reverse_fingers[node_id]:
        smv = smv + f"            node{k}.mode = waiting & node{i}.mode = next_node & node{i}.index = {j} : find_successor ;\n"
    smv = smv + next_node_p2.format(idx=k)

smv = smv + "LTLSPEC\n"
for i, node_id in enumerate(node_ids):
    next_i = (i + 1) % len(node_ids)
    smv = smv + f"    ((n > {node_id} & n <= {node_ids[next_i]}) -> (F node{i}.mode = found_successor))"
    if i != NUM_NODES - 1:
        smv = smv + " &\n"

smv = smv + ";\n\n"

smv = smv + "LTLSPEC\n"
smv = smv + "     F G (\n"
for i in range(0, NUM_NODES):
    smv = smv + \
          "         ("
    for j in range(0, NUM_NODES):
        if i == j:
            smv = smv + f" node{j}.mode = found_successor "
        else:
            smv = smv + f" node{j}.mode = waiting "

        if j != NUM_NODES - 1:
            smv = smv + "&"

    smv = smv + ")"
    if i != NUM_NODES - 1:
        smv = smv + " |\n"
    else:
        smv = smv + ");\n\n"

for k, node_id in enumerate(node_ids):
    smv = smv + "LTLSPEC\n"
    smv = smv + f"    G (node{k}.mode = next_node -> X ("
    for i, j in enumerate(fingers[k]):
        smv = smv + f"node{j}.mode = find_successor"
        if i != len(fingers[k]) - 1:
            smv = smv + " xor "
    smv = smv + "));\n\n"

smv = smv + "INVARSPEC\n"

for i in range(0, NUM_NODES):
    smv = smv + f"    node{i}.mode != waiting"
    if i != NUM_NODES - 1:
        smv = smv + " xor\n"
smv = smv + ";\n\n"     # TODO: remove this line? No still need newlines

for i in range(0, NUM_NODES):
    smv = smv + "LTLSPEC\n"
    smv = smv + f"    G ((node{i}.mode = get_next_finger & X (node{i}.mode = find_successor)) -> node{i}.id = n);\n\n"

smv = smv + f"""
MODULE node(id_i, successor_id_i, fingers_i)

  FROZENVAR
    id : 0..{MAX_ID};
    successor_id : 0..{MAX_ID};

  VAR
    index : -1..{NUM_BITS};
    mode : {{
      waiting,
      find_successor,
      found_successor,
      closest_preceding,
      get_next_finger,
      test_finger,
      next_node
    }};

  DEFINE
    fingers := fingers_i;

  ASSIGN
    init(id) := id_i;
    init(successor_id) := successor_id_i;
    init(index) := {NUM_BITS};

    next(index) :=
      case
        index = -1 : {NUM_BITS};
        mode = get_next_finger : index - 1;
        TRUE : index ;
      esac;

INVARSPEC
  mode = closest_preceding -> index = {NUM_BITS}
  
LTLSPEC
  G ((mode = get_next_finger & X (mode = find_successor)) -> X (X (mode = found_successor)))

LTLSPEC
  G ((mode = find_successor) -> X (mode = found_successor | mode = closest_preceding)) &
  G ((mode = waiting) -> X (mode = find_successor | mode = waiting)) &
  G ((mode = closest_preceding) -> X (mode = get_next_finger)) &
  G ((mode = get_next_finger) -> X (mode = test_finger | mode = find_successor)) &
  G ((mode = test_finger) -> X (mode = get_next_finger | mode = next_node)) &
  G ((mode = next_node) -> X (mode = waiting));
"""

print(smv)
