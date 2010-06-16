import nltk
from itertools import chain, combinations

USE_LEMMATIZATION = True

current_id = 0

def minimal_linked_subtrees(tree1, tree2):
	# Takes out shared subtrees from tree1 and tree2, until nothing is left.
	# Then decomposes the shared subtrees into rules linked to themselves.
	# Then links the remaining (unmatchable) part of tree1 to tree2.

	shared_subtrees = True # Are there any shared subtrees?
	linked_subtrees = []
	tree1 = tree1.copy(True) # (deep copy)
	tree2 = tree2.copy(True) # (deep copy)

	while(shared_subtrees):
		max_shared_subtree_size = 0 # The size of the maximal shared subtree
		max_shared_subtree = None
		for (parent1, num1, i) in my_subtrees(tree1):
			for (parent2, num2, j) in my_subtrees(tree2):
				if i == j and type(i) == nltk.Tree:
					# check if larger than current maximal tree, etc.
					if len(i.leaves()) > max_shared_subtree_size:
						max_shared_subtree_size = len(i.leaves())
						max_shared_subtree = (i, parent1, num1, parent2, num2)

		# If no subtree is found yet, find an 'almost-match' (e.g. a
		# conjugation)
		if USE_LEMMATIZATION and max_shared_subtree == None:
			for (parent1, num1, i) in my_subtrees(tree1):
				for (parent2, num2, j) in my_subtrees(tree2):
					if type(i) == nltk.Tree and type(j) == nltk.Tree and
						i.node == j.node and i.node[0] == 'V' # starts with V
						len(i) == len(j) == 1 and
						lemma(i[0]) == lemma(j[0]):
							pass

		# Remove the shared subtree from the tree...
		if max_shared_subtree:
			(tree, parent1, num1, parent2, num2) = max_shared_subtree
			# Decorate tree with ids.
			tree = decorate_with_ids(tree)
			parent1[num1] = tree.node # nltk.Tree(tree.node, [])
			parent2[num2] = tree.node # nltk.Tree(tree.node, [])

		if max_shared_subtree == None:
			shared_subtrees = False
		else:
			linked_subtrees.append(tree)

	# Decompose linked subtrees into minimal subtrees (so far: these always are
	# PCFG-rules)
	minimal_subtrees = []
	for i in linked_subtrees:
		for j in i.productions():
			minimal_subtrees.append(
				(production_to_tree(j), production_to_tree(j)))

	minimal_subtrees.append((tree1, tree2))
	return minimal_subtrees

def linked_subtrees_to_probabilistic_rules(linked_subtrees):
	# Add 'links' between leaf nodes.
	linked_subtrees2 = []
	for (t1, t2) in linked_subtrees:
		l1 = filter(lambda x: '@' in x, t1.leaves())
		l2 = filter(lambda x: '@' in x, t2.leaves())
		a = [(l1.index(x), l2.index(x)) for x in l1]
		linked_subtrees2.append((t1, t2, a))

	# For every addressed node, look at possible ways to remove id again.
	# Find addressed leaf-positions
	# Add frequency counts
	newtrees = []
	for (t1, t2, links) in linked_subtrees2:
		print "\nOriginal trees:\n1: %s\n2: %s\n" % (t1, t2)
		leafindex1 = frontier_nodes(t1)
		leafindex2 = frontier_nodes(t2)
		print "Leafindices:\n1: %s\n2: %s\n" % (leafindex1, leafindex2)

		indices12 = [(leafindex1[l], leafindex2[l], l) for l in leafindex1.keys()]
		for a in sublists(indices12):
			leaves = [b[2] for b in a]
			newtree1 = t1.copy(True)
			newtree2 = t2.copy(True)
			for (l, r, leaf) in a:
				newtree1[l] = rmid(newtree1[l])
				newtree2[r] = rmid(newtree2[r])
			newtrees.append(
				(newtree1, newtree2, links,
				product(count(leaf, linked_subtrees) for leaf in leaves)))
			print "Tree pair:\n1: %s\n2: %s\n" % (newtree1, newtree2)
			if "@" in newtree1.node:
				newtree1a = newtree1.copy(True)
				newtree2a = newtree2.copy(True)
				newtree1a.node = rmid(newtree1.node)
				newtree2a.node = rmid(newtree2.node)
				newtrees.append(
					(newtree1a, newtree2a, links,
					product(count(leaf, linked_subtrees) for leaf in leaves)) )
				print "Tree pair:\n1: %s\n2: %s\n" % (newtree1a, newtree2a)
				
	return newtrees

def leaves_and_frontier_nodes(tree):
	leaves = [] 
	for child in tree: 
		if isinstance(child, nltk.Tree) and len(child) > 0: 
			leaves.extend(leaves_and_frontier_nodes(child)) 
		else: 
			leaves.append(child) 
	return leaves 

def my_flatten(tree):
	return nltk.Tree(tree.node, leaves_and_frontier_nodes(tree))

def count(our_node, linked_subtrees):
	for (a, b) in linked_subtrees:
		if a.node == our_node:
			return product([
				count(b, linked_subtrees) + 1 for
				b in frontier_nodes(a).keys()])
	return -1

def frontier_nodes(tree):
	return dict((l, p) for l, p
		in zip(tree.leaves(), tree.treepositions('leaves')) if '@' in l)

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
		a.node = "%s@%d" % (a.node, current_id)
		current_id += 1
	return utree

def production_to_tree(production):
	return nltk.Tree(str(production.lhs()), [str(r) for r in production.rhs()])

def my_subtrees(tree): 
	for (n, child) in zip(range(len(tree)), tree): 
		yield (tree, n, child)
		if isinstance(child, nltk.tree.Tree): 
			for subtree in my_subtrees(child): 
				yield subtree

def test():
	tree1 = nltk.Tree("(S (NP John) (VP (V bought) (NP (DET a) (N car))))")
	tree2 = nltk.Tree("(S (VBZ did) (NP John) (VP (V buy) (NP (DET a) (N car))))")
	t = minimal_linked_subtrees(tree1, tree2)
	for a in t: print a
	t2 = linked_subtrees_to_probabilistic_rules(t)
	print
	print
	for b in t2:
		for c in b: print c
		print

def test2():
	tree1 = nltk.Tree("(S (NP mary) (VP walks))")
	tree2 = nltk.Tree("(S (NP mary) (VP walks))")
	t = minimal_linked_subtrees(tree1, tree2)
	for a in t: print a
	t2 = linked_subtrees_to_probabilistic_rules(t)
	print
	print
	for b in t2:
		for c in b: print c
		print
