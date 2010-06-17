import nltk
import grammardict
from nltk import Tree
from itertools import chain, combinations

USE_LEMMATIZATION = True

current_id = 0

def minimal_linked_subtrees(tree1, tree2):
	# Takes out shared subtrees from tree1 and tree2, until nothing is left.
	# Then decomposes the shared subtrees into rules linked to themselves.
	# Then links the remaining (unmatchable) part of tree1 to tree2.

	shared_subtrees = True # Are there any shared subtrees?
	linked_subtrees = []
	equivalents = []
	tree1 = tree1.copy(True) # (deep copy)
	tree2 = tree2.copy(True) # (deep copy)

	while(shared_subtrees):
		max_shared_subtree_size = 0 # The size of the maximal shared subtree
		max_shared_subtree = None
		lemmatized_equivalents = None
		for (parent1, num1, i) in my_subtrees(tree1):
			for (parent2, num2, j) in my_subtrees(tree2):
				if i == j and type(i) == Tree:
					# check if larger than current maximal tree, etc.
					if len(leaves_and_frontier_nodes(i)) > max_shared_subtree_size:
						max_shared_subtree_size = len(leaves_and_frontier_nodes(i)) 
						max_shared_subtree = (i, parent1, num1, parent2, num2)

		# If no subtree is found yet, find an 'almost-match' (e.g. a
		# conjugation)
		if USE_LEMMATIZATION and max_shared_subtree == None:
			wnl = nltk.stem.WordNetLemmatizer() 
			for (parent1, num1, i) in my_subtrees(tree1):
				if type(i) == Tree and len(i) == 1 and type(i[0]) == str:
					for (parent2, num2, j) in my_subtrees(tree2):
						if (type(j) == Tree and
							i.node == j.node and i.node[0] == 'V' and # starts with V
							len(j) == 1 and type(j[0]) == str and
							wnl.lemmatize(i[0], 'v') == wnl.lemmatize(j[0], 'v')):
								lemmatized_equivalents = (i, j, parent1, num1,
									parent2, num2)

		# Remove the shared subtree from the tree...
		if max_shared_subtree:
			(tree, parent1, num1, parent2, num2) = max_shared_subtree
			# Decorate tree with ids.
			tree = decorate_with_ids(tree)
			parent1[num1] = Tree(tree.node, []) # tree.node
			parent2[num2] = Tree(tree.node, []) # tree.node
		elif lemmatized_equivalents:
			(i, j, parent1, num1, parent2, num2) = lemmatized_equivalents
			(i, j) = decorate_pair(i, j)
			parent1[num1] = Tree(i.node, [])
			parent2[num2] = Tree(j.node, [])
		
		if lemmatized_equivalents:
			equivalents.append((i, j))
		elif max_shared_subtree == None:
			shared_subtrees = False
		else:
			linked_subtrees.append(tree)

	# Decompose linked subtrees into minimal subtrees (so far: these always are
	# PCFG-rules)
	minimal_subtrees = []
	for i in linked_subtrees:
		for j in i.productions():
			if len(j.rhs()) > 0:
				minimal_subtrees.append(
					(production_to_tree(j), production_to_tree(j)))

	for (x, y) in equivalents:
		minimal_subtrees.append((x, y))

	minimal_subtrees.append((tree1, tree2))
	return minimal_subtrees

def linked_subtrees_to_probabilistic_rules(linked_subtrees):
	# Add 'links' between leaf nodes.
	linked_subtrees2 = []
	for (t1, t2) in linked_subtrees:
		l1 = filter(lambda x: (type(x) == Tree and '@' in x.node), leaves_and_frontier_nodes(t1))
		l2 = filter(lambda x: (type(x) == Tree and '@' in x.node), leaves_and_frontier_nodes(t2))
		# Very ugly, but might be needed to guarantee the right outcome...
		a = [(l1.index(x), l2.index(x)) for x in l1]
		a.sort
		a = [x[1] for x in a] 
		linked_subtrees2.append((t1, t2, a))

	# For every addressed node, look at possible ways to remove id again.
	# Find addressed leaf-positions
	# Add frequency counts
	newtrees = []
	for (t1, t2, links) in linked_subtrees2:
		leafindex1 = dict(frontier_nodes(t1))
		leafindex2 = dict(frontier_nodes(t2))

		indices12 = [(leafindex1[l], leafindex2[l], l) for l in leafindex1.keys()]
		for a in sublists(indices12):
			leaves = [str(b[2]) for b in indices12 if not (b in a)]
			newtree1 = t1.copy(True)
			newtree2 = t2.copy(True)
			for (l, r, leaf) in a:
				newtree1[l].node = rmid(str(newtree1[l].node))
				newtree2[r].node = rmid(str(newtree2[r].node))
			newtrees.append(
				(newtree1, newtree2, links,
				product(count(leaf, linked_subtrees) for leaf in leaves)))
			if "@" in newtree1.node:
				newtree1a = newtree1.copy(True)
				newtree2a = newtree2.copy(True)
				newtree1a.node = str(rmid(newtree1.node))
				newtree2a.node = str(rmid(newtree2.node))
				newtrees.append(
					(newtree1a, newtree2a, links,
					product(count(leaf, linked_subtrees) for leaf in leaves)) )
				
	return newtrees

def leaves_and_frontier_nodes(tree):
	leaves = [] 
	for child in tree: 
		if isinstance(child, Tree) and len(child) > 0: 
			leaves.extend(leaves_and_frontier_nodes(child)) 
		else: 
			leaves.append(child) 
	return leaves 

def my_flatten(tree):
	return Tree(tree.node, leaves_and_frontier_nodes(tree))

def count(our_node, linked_subtrees):
	for (a, b) in linked_subtrees:
		if str(a.node) == our_node:
			return product([
				count(str(c), linked_subtrees) + 1 for
				c in dict(frontier_nodes(a)).keys()])
	return -1

def frontier_nodes(tree):
	if frontier_node(tree):
		return [(tree.node, ())]
	elif type(tree) == str:
		return []
	else:
		fnodes = []
		for (stree, pos) in zip(tree, range(len(tree))):
			fnodes += [(fnode, ((pos,) + r)) for (fnode, r) in frontier_nodes(stree)]
		return fnodes

#def frontier_nodes(tree):
#	return dict((l, p) for l, p
#		in zip(tree.leaves(), tree.treepositions('leaves')) if '@' in l)

def frontier_node(tree):
	return (type(tree) == Tree and len(tree) == 0)

def product(l):
	return reduce(lambda x, y: x * y, l, 1)

def sublists(l):
	return chain(
		reduce(chain, (combinations(l, a) for a in range(len(l))), () ), (l,))

def rmid(x):
	return x.split("@")[0]

def decorate_with_ids(tree):
	global current_id
	utree = tree.copy(True)
	for a in utree.subtrees():
		if not ("@" in a.node):
			a.node = "%s@%d" % (a.node, current_id)
			current_id += 1
	return utree

def decorate_pair(tree1, tree2):
	global current_id
	utree1 = tree1.copy(True)
	utree2 = tree2.copy(True)
	utree1.node = "%s@%d" % (utree1.node, current_id)
	utree2.node = "%s@%d" % (utree2.node, current_id)
	current_id += 1
	return (utree1, utree2)

def treeify(node):
	if type(node) == nltk.grammar.Nonterminal:
		return Tree(str(node), [])
	else:
		return node
	
def production_to_tree(production):
	return Tree(str(production.lhs()), [treeify(r) for r in production.rhs()])

def my_subtrees(tree): 
	for (n, child) in zip(range(len(tree)), tree): 
		yield (tree, n, child)
		if isinstance(child, Tree): 
			for subtree in my_subtrees(child): 
				yield subtree

def test():
	tree1 = Tree("(S (NP John) (VP (V bought) (NP (DET a) (N car))))")
	tree2 = Tree("(S (VBZ did) (NP John) (VP (V buy) (NP (DET a) (N car))))")
	t = minimal_linked_subtrees(tree1, tree2)
	for a in t: print a
	t2 = linked_subtrees_to_probabilistic_rules(t)
	print
	print
	for b in t2:
		for c in b: print c
		print
	gr = grammardict.TransformationDOP()
	gr.add_to_grammar(t2)
	gr.print_grammar()
	a = gr.get_grammar()
	return a

def add_to_grammar(gr, tree1, tree2):
	t = minimal_linked_subtrees(tree1, tree2)
	t2 = linked_subtrees_to_probabilistic_rules(t)
	gr.add_to_grammar(t2)

def test2():
	tree1 = Tree("(S (NP mary) (VP walks))")
	tree2 = Tree("(S (NP mary) (VP walks))")
	t = minimal_linked_subtrees(tree1, tree2)
	for a in t: print a
	t2 = linked_subtrees_to_probabilistic_rules(t)
	print
	print
	for b in t2:
		for c in b: print c
		print

def test3():
	corpus = """(S (NP John) (VP (V bought) (NP (DET a) (N car))))
	 (S (VBZ did) (NP John) (VP (V buy) (NP (DET a) (N car))))
""".splitlines()
	corpus = map(Tree, corpus)
	corpus = zip(corpus[::2], corpus[1::2])

	gr = grammardict.TransformationDOP()
	for x, y in corpus:
		add_to_grammar(gr, x, y)
	return gr

# (Tree('NP@0', ['DET@1', 'N@2']), Tree('NP@0', ['DET@1', 'N@2']))
# (Tree('DET@1', ['a']), Tree('DET@1', ['a']))
# (Tree('N@2', ['car']), Tree('N@2', ['car']))
# (Tree('NP@3', ['John']), Tree('NP@3', ['John']))
# (Tree('VP@5', ['V@4', 'NP@0']), Tree('VP@5', ['V@4', 'NP@0']))
# (Tree('V@4', ['bought']), Tree('V@4', ['buy']))
# (Tree('S', ['NP@3', 'VP@5']), Tree('S', [Tree('VBZ', ['did']), 'NP@3', 'VP@5']))
