import nltk

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
		if max_shared_subtree == None:
			pass

		# Remove the shared subtree from the tree...
		if max_shared_subtree:
			(tree, parent1, num1, parent2, num2) = max_shared_subtree
			parent1[num1] = str(tree.node)
			parent2[num2] = str(tree.node)

		if max_shared_subtree == None:
			shared_subtrees = False
		else:
			linked_subtrees.append(max_shared_subtree[0])

	# Decompose linked subtrees into minimal subtrees (so far: these always are
	# PCFG-rules)
	minimal_subtrees = []
	for i in linked_subtrees:
		for j in i.productions():
			minimal_subtrees.append(
				(production_to_tree(j), production_to_tree(j)))

	minimal_subtrees.append((tree1, tree2))
	return minimal_subtrees

def production_to_tree(production):
	return nltk.Tree(str(production.lhs()), [str(r) for r in production.rhs()])

def my_subtrees(tree): 
	for (n, child) in zip(range(len(tree)), tree): 
		yield (tree, n, child)
		if isinstance(child, nltk.tree.Tree): 
			for subtree in my_subtrees(child): 
				yield subtree

# tree1 = nltk.Tree("(S (NP John) (VP (V bought) (NP (DET a) (N car))))")
# tree2 = nltk.Tree("(S (VBZ did) (NP John) (VP (V buy) (NP (DET a) (N car))))")
# bla.minimal_linked_subtrees(tree1, tree2)
