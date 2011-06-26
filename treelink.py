from bitpar import BitParChartParser
from nltk import memoize
from nltk import Tree, WeightedProduction, WeightedGrammar, edit_distance, \
	ViterbiParser, FreqDist, WordNetLemmatizer, Nonterminal, ImmutableTree
from nltk.metrics import f_measure, precision, recall
from itertools import chain, combinations, product, permutations
from math import log
from operator import mul
from collections import defaultdict
from random import sample
from sys import argv
from heapq import heappush, heappop, nlargest
from numpy import std, mean
USE_LEMMATIZATION = True
# number of partial subtree matches to consider:
NUM_PARTIAL = 10
# whether to make sure a substitution is allowed on the target side (otherwise only the source side is checked)
global CHECK_SUBSTITUTION
CHECK_SUBSTITUTION = False
wnl = WordNetLemmatizer()

# [3~{(S=#i[P=0.25] #1=(NP=#i[P=1] mary)(VP=#i[P=0.5] #2=(VB=#i[P=1] walks) #3=(RB=#i[P=1] quickly)))#i(S=#i[P=0.25] #1(S1=#i[P=0.5](VP=#i[P=0.5] #2) #3))}
current_id = 1
def topdownparse(grammar, sent, root="top"):
	# Roark's Fully-Connected Parsing Algorithm
	# not working yet.
	# Python's heapq is a min-heap, so we do everything with negative numbers.
	def above_threshold(h, C, N):
		if h[0] < -0.00005: return True
	def LAP(t1, w1): return -1.0
	C, N = [], []
	h = (q, r, t) = (-1, -1, Tree(root, []))
	C.append((q, r, t))
	for i,w in enumerate(sent):
		while above_threshold(h, C, N):
			h = heappop(C)
			for x in (x for x in grammar if x.prob() * -q > 0): # ??
				q1 = q * x.prob() # ??
				t1 = join(t, production_to_tree(x))
				if t1 == None: continue
				if x.rhs()[0] == w:
					w1 = sent[i+1]
					r1 = LAP(t1, w1)
					h1 = (q1, r1, t1)
					heappush(N, h1)
				else:
					w1 = w
					r1 = LAP(t1, w1)
					h1 = (q1, r1, t1)
					heappush(C, h1)
		C = []
		C, N = N, C
	prob, foo, tree = heappop(C)
	return tree, prob

def mytopdownparse(grammar, sent, t=None, depth=1, depthlimit=3):
	# primitive topdown parser
	if t == None: t = Tree("top", [])
	if depth >= depthlimit: raise StopIteration
	substitution_sites = [a.node for a in t.subtrees() if len(a) == 0]
	if substitution_sites:
		leftmost = Nonterminal(substitution_sites[0])
		candidates = [a for a in grammar._lhs_index[leftmost]]
		# ^^... if sent[0] in grammar._leftcorners[a.lhs()]]
		rec, nonrec = [], []
		for a in candidates:
			if a.lhs() in a.rhs(): rec.append(a)
			else: nonrec.append(a)
		for x in nonrec:
			t1 = join(t, production_to_tree(x))
			if t1.leaves() != sent[:len(t1.leaves())]: continue
			grammar._lhs_index[leftmost].remove(x)
			grammar._lhs_index[leftmost].append(x)
			for a, p in mytopdownparse(grammar, sent[len(t1.leaves()):],
				t1, depth):
				yield a, x.prob() * p
		for x in rec:
			t1 = join(t, production_to_tree(x))
			if t1.leaves() != sent[:len(t1.leaves())]: continue
			grammar._lhs_index[leftmost].remove(x)
			grammar._lhs_index[leftmost].append(x)
			for a, p in mytopdownparse(grammar, sent[len(t1.leaves()):],
				t1, depth+1):
				yield a, x.prob() * p
	elif t.leaves() == sent: yield t, 1
			
def join(a, b):
	for c in a.treepositions():
		# non-terminal node, same label as b, empty node
		if isinstance(a[c], Tree) and a[c].node == b.node and len(a[c]) == 0:
			d = a.copy(True)
			d[c].extend(b)
			return d

class TransformationDOP:
	def __init__(self):
		self.grammardict = defaultdict(FreqDist)
		self.mygrammardict = defaultdict(FreqDist)
		self.fd = FreqDist()
		self.mangled = {}

	def add_to_grammar(self, mlsts, source="left"):
		# Adds the minimal linked subtrees (mlsts) to the grammar.
		print "adding to grammar"
		for (lefttree, righttree, links, count) in mlsts:
			if source == "right":
				lefttree, righttree = righttree, lefttree
			righttree = righttree.freeze()
			links = tuple(links)
			flattened_tree = my_flatten(lefttree)
			index = filter(lambda x: len(x.rhs()) > 0,
							flattened_tree.productions())[0]
			self.grammardict[index].inc((righttree, links), count)
			self.mygrammardict[lefttree.freeze()].inc((righttree, links), count)
			self.fd.inc(index.lhs(), float(count))

	def sort_grammar(self, withids=False):
		# sort the grammar by fragment size, largest first
		if withids:
			self.mygrammarsorted = sorted((a
						for a in self.mygrammardict.keys()),
						key=lambda x: len(x.treepositions()),
						reverse=True)
		else:
			self.mygrammarsorted = sorted(set(undecorate_with_ids(a).freeze()
						for a in self.mygrammardict.keys()),
						key=lambda x: len(x.treepositions()),
						reverse=True)

	def extendlex(self, corpus):
		# collect all preterminals and terminals from a corpus, add them as
		# linked subtrees.
		for a,b in corpus:
			blem = dict((wnl.lemmatize(w, "v"), (w,p)) for w,p in b.pos())
			for word, pos in a.pos():
				lem = wnl.lemmatize(word, "v")
				if wnl.lemmatize(word, "v") in blem:
					right = ImmutableTree(blem[lem][1], [blem[lem][0]])
				else:	right = ImmutableTree(pos, [word])
				left = ImmutableTree(pos, [word])
				x = left.productions()[0]
				self.grammardict[x].inc((right, ()))
				self.mygrammardict[left].inc((right, ()))
				self.fd.inc(x.lhs(), 1.)

	def print_grammar(self):
		for (key, value) in self.grammardict.items():
			print "Source rule: %s\n" % key
			for ((tree, links), count) in value.items():
				print "  Tree: %s" % tree
				print "  Links: %s" % repr(links)
				print "  Count: %d\n" % count
			print

	def get_grammar(self, freqfn=sum, prob=True, bitpar=False, root="S"):
		# Returns a PCFG. (Use freqfn=max for most likely derivation, 
		#	prob=sum for most likely parse)  <-- this can't be correct.
		grammar = [ WeightedProduction(key.lhs(), key.rhs(),
						prob=freqfn(count for (tree, links), count
							in value.items()))
						for key, value in self.grammardict.items() ]
		if prob:
			if bitpar:
				grammar = []
				lexicon = set()
				#	list(chain(*((
				#		(a, key.lhs()
				#			if len(key.rhs()) == 1 
				#			else str(key.lhs())+"_"+str(a))
				#		for a in key.rhs()
				#		if not isinstance(a, Nonterminal))
				#	for key in self.grammardict)))
				for key, value in self.grammardict.items():
					count = freqfn(value.values())
					tmp = forcepos(production_to_tree(key))
					tmp.chomsky_normal_form()
					lexicon.update(tmp.pos())
					for a in tmp.productions():
						if len(a.rhs()):
							grammar.append(("%s\t%s" % (str(a.lhs()),
										"\t".join(map(str, a.rhs()))), count))
				return grammar, list(lexicon)
			else:
				grammar = [WeightedProduction(key.lhs(), key.rhs(),
					prob=freqfn(value.values()) / self.fd[key.lhs()])
					for key, value in self.grammardict.items()]
				return WeightedGrammar(Nonterminal(root), grammar)
		else:
			return grammar
	
	def get_my_grammar(self, bitpar=False, root="S"):
		grammar = FreqDist()
		lexicon = list(reduce(chain, (tree.leaves() for tree
									in self.mygrammardict)))
		for key, value in self.mygrammardict.items():
			count = max(value.values())
			tmp = Tree.convert(key)
			if bitpar: forcepos(tmp).chomsky_normal_form()
			for a in tmp.productions():
				if len(a.rhs()):
					if bitpar:
					# fixme: proper goodman frequencies here of course
						grammar.inc("%s\t%s" % (str(a.lhs()),
								"\t".join(map(str, a.rhs()))), count)
					else:
						grammar.inc(a, count)
		if bitpar:
			return grammar.items(), lexicon
		fd = FreqDist()
		for k,v in grammar.items(): fd.inc(k.lhs(), v)
		return WeightedGrammar(Nonterminal(root),
				[WeightedProduction(k.lhs(), k.rhs(),
					prob=v/float(fd.get(k.lhs(),v)))
					for k,v in grammar.items()])
		
			
	def my_mlt_deriv(self, tree, allowpartial=False):
		# translation using subtrees instead of flattened trees
		def match(tree, candidate):
			# walk through candidate and compare to tree
			for idx in candidate.treepositions():
				try:
					if tree[idx] == candidate[idx]: continue
					if tree[idx].node != candidate[idx].node: return False
					if len(candidate[idx]) not in (0, len(tree[idx])):
						return False
				except: return False
			return True
		def similarity(tree, candidate):
			# walk through candidate and compare to tree
			# same node at same index is full points, same node at a different
			# index in the same constituent is half points, weighted by height
			# with higher nodes having more weight.
			sim = 0.0
			h = float(candidate.height())
			links = {}
			for idx in sorted(candidate.treepositions()[1:], key=len):
				try:
					if (isinstance(candidate[idx], str)
						and tree[idx] == candidate[idx]):
						sim += 1 #* (candidate[idx].height() / h)
					elif (isinstance(candidate[idx], str)
						and candidate[idx] not in tree.leaves()):
						return 0, {}
					if (candidate[idx].node in 
						[a.node for a in tree[idx[:-1]]]):
						sim += 0.5 #* (candidate[idx].height() / h)
					if tree[idx].node == candidate[idx].node:
						sim += 0.5 #* (candidate[idx].height() / h)
					# align all nodes of this type in a greedy fashion
					matches = [n for n, a in enumerate(tree[idx[:-1]]) if a.node == candidate[idx].node]
					competing = [n for n, a in enumerate(candidate[idx[:-1]]) if a.node == candidate[idx].node]
					for n in matches:
						nearest = min(((m - n), m) for m in competing)[1]
						links[idx[:-1] + (nearest,)] = idx[:-1] + (n,)
						competing.remove(nearest)
				except: pass
				# no similarity at level directly under parent => fail
				if len(idx) > 0 and sim == 0: return 0, {}
				# other idea: similarity should be nonzero within each constituent
			a = sim / len(tree.treepositions())
			b = sim / len(candidate.treepositions())
			# harmonic mean
			result = (2 * a * b) / (a + b)
			return result, links

		yielded = False
		matched = False
		for candidate in self.mygrammarsorted:
			if match(tree, candidate):
				matched = True
				for righttree, links in self.mygrammardict[candidate]:
					count = self.mygrammardict[candidate][(righttree, links)]
					lhscount = self.fd.get(Nonterminal(candidate.node), count)
					target = Tree.convert(righttree)
					lfrontiers = list(frontier_nodes(candidate))
					frontiers = list(frontier_nodes(righttree))
					if not lfrontiers:
						#print "no frontiers", target, count, "/", lhscount
						yield target, count / lhscount
						yielded = True
						continue
					#new_subtree_forest = product(*(self.my_mlt_deriv(tree[a[1]]) for a in lfrontiers))
					#new_subtree_forest = list(product(*[list(self.my_mlt_deriv(tree[a[1]])) for a in lfrontiers]))
					new_subtree_forest = []
					for a in lfrontiers:
						new_subtree_forest.append(list(self.my_mlt_deriv(tree[a[1]], allowpartial)))
					new_subtree_forest = list(product(*new_subtree_forest))
					for new_subtrees in new_subtree_forest:
						target = Tree.convert(righttree)
						for (subtree, freq), index in zip(new_subtrees, links):
							idx = frontiers[index][1]
							# check if substitution is on a matching node, 
							if not CHECK_SUBSTITUTION or subtree.node == target[idx].node:
								target[frontiers[index][1]] = subtree
							else:
							#	print "illegal righttree; expected", target[idx].node, "got", subtree
								break
						else:
							prob = count / lhscount * reduce(mul, (a[1] for a in new_subtrees), 1)
							#print "used", candidate, "=>", righttree
							yield target, prob
							yielded = True
						#if target.node == "top": break # stop deriving after first full derivation
					#else: continue # with other right trees
					#break
				#else: continue # with other candidates (left trees)
				#break
		if not yielded and tree.node not in ("top", "s", "sq", "vp"):
			#found nothing, do smoothing
			#print "smoothing for", tree
			yield tree, 1 / self.fd.get(Nonterminal(tree.node))
		elif (not matched) and allowpartial and len(tree):
			# do partial match here
			#score, candidate = sorted([(similarity(tree, a), a) for a in self.mygrammardict if a.node == tree.node])[-1]
			partial = sorted([(similarity(tree, a), a) for a in self.mygrammarsorted if a.node == tree.node], reverse=True)[:NUM_PARTIAL]
			#print "partial matches for", tree
			#for s,p in partial: print s, p
			for (score, links), candidate in partial:
				if score == 0: break
				if any(a not in tree.leaves() for a in candidate.leaves()):
					#print "spurious match", score, links, candidate
					continue

				#print "partial match", score, candidate
				# now rewrite candidate with subtrees from our tree to be translated
				newtree = Tree.convert(candidate)
				covered, notcovered = [], []
				frontiers = frontier_nodes(newtree)
				frontiers.sort(key=lambda x: len(x[1]))
				fnodes = [a[0] for a in frontiers]
				nnodes = [newtree[a].node for a in newtree.treepositions() if isinstance(newtree[a], Tree)]
				# get nodes and indices of current tree that are frontier nodes in the new tree or that don't exist there
				# sort by length of index, so that nodes are sorted by level (highest nodes first)
				# actually we should calculate a proper tree alignment and link each of the nodes
				indices = [a for a in tree.treepositions() if isinstance(tree[a], Tree) 
						and (tree[a].node in fnodes or tree[a].node not in nnodes)]
				indices.sort(key=len)
				nodes = [tree[a].node for a in indices]
				for node, idx in frontiers:
					if idx in links:
						oldidx = links[idx]
						del links[idx]
						newtree[idx] = tree[oldidx]
						# remove the node we just inserted and all of its children, and its parent
						indices = [a for a in indices if a[:len(oldidx)] != oldidx and a != oldidx[:-1]]
						nodes = [tree[a].node for a in indices]
						covered.append(node)
				if not covered: continue
				# leftovers not part of our match (recover normal order again):
				notcovered = [a for a in tree.treepositions() if a in indices]
				# veto any partial match if it does not contain a match for the main verb in the original tree (if any)
				verbheads = "md vbz vbp vbd vb".split()
				if any(a in nodes for a in verbheads) and not any(a in covered for a in verbheads): continue
				#print "notcovered", notcovered, "newtree", newtree
				for deriv,prob in self.my_mlt_deriv(newtree, allowpartial):
					if deriv.leaves() == []: continue
					#print "deriv", deriv
					result = munge(deriv, tree, indices)
					self.mangled[(deriv.freeze(), tree.freeze(), tuple(indices))] = result
					#print "munged", result
					yield result, prob * score #1 / self.fd[Nonterminal(tree.node)]
				#	break
		#elif not yielded: print "no cigar", tree

	def get_mlt_deriv_multi(self, tree, smoothing=False, verbose=False):
		# Iterator over translations of tree
		top_production = tree.productions()[0]
		if top_production in self.grammardict:
			candidates = self.grammardict[top_production].items()
		elif smoothing:
			if verbose: print "not found", top_production
			candidates = [((production_to_tree(top_production), [n for n,a in enumerate(a for a in tree if isinstance(a, Tree))]), 1.)]
		else:
			if verbose: print "not found", top_production
			raise StopIteration
		#this lookup shouldn't fail silently
		if top_production.lhs() in self.fd:
			lhscount = self.fd[top_production.lhs()]
		else: raise ValueError(" %s not in fd " % top_production.lhs())
		#new_subtree_forest = list(product(*(self.get_mlt_deriv_multi(a, smoothing, verbose) for a in tree if isinstance(a, Tree))))
		new_subtree_forest = list(product(*(self.get_mlt_deriv_multi(a, smoothing, verbose) for a in tree if isinstance(a, Tree))))
		if verbose:
			print "subtree forest"
			for a in new_subtree_forest:
				if not a: continue
				print "<",
				for b in a: print b
				print ">"
		yielded = False
		# Add new subtrees
		for (righttree, links), count in candidates:
			#if verbose: print "using", righttree, "for", tree
			prob = log(count / lhscount)
			assert(count > 0)
			frontiers = frontier_nodes(righttree)
			for new_subtrees in new_subtree_forest:
				target = Tree.convert(righttree)
				for n, index in enumerate(links):
					# check if substitution is on a matching node, 
					match = (new_subtrees[n][0].node == target[frontiers[index][1]].node)
					if not CHECK_SUBSTITUTION or match:
						target[frontiers[index][1]] = new_subtrees[n][0]
						if verbose: print "substituted", new_subtrees[n][0]
					else:
						if verbose:
							print new_subtrees[n][0], "does not fit with", target, "source", tree
							print "candidates", candidates
						break
					if not match: prob -= 4		#penalty for incorrect label
				else:
					prob += sum(prob for a,prob in new_subtrees)
					yield target, prob
					yielded = True
		if smoothing and not yielded:
			righttree, links, count = production_to_tree(top_production), [n for n,a in enumerate(a for a in tree if isinstance(a, Tree))], 0.5
			#if verbose: print "using", righttree, "for", tree
			prob = log(count / lhscount)
			assert(count > 0)
			frontiers = frontier_nodes(righttree)
			for new_subtrees in new_subtree_forest:
				target = Tree.convert(righttree)
				for n, index in enumerate(links):
					# check if substitution is on a matching node, 
					match = (new_subtrees[n][0].node == target[frontiers[index][1]].node)
					if not CHECK_SUBSTITUTION or match:
						target[frontiers[index][1]] = new_subtrees[n][0]
						if verbose: print "substituted", new_subtrees[n][0]
					else:
						if verbose:
							print new_subtrees[n][0], "does not fit with", target, "source", tree
							print "candidates", candidates
						break
					if not match: prob -= 4		#penalty for incorrect label
				else:
					prob += sum(prob for a,prob in new_subtrees)
					yield target, prob
					yielded = True
				
def minimal_linked_subtrees(tree1, tree2, decorate=True, alignments=None):
	# Takes out shared subtrees from tree1 and tree2, until nothing is left.
	# Then decomposes the shared subtrees into rules linked to themselves.
	# Then links the remaining (unmatchable) part of tree1 to tree2.
	if not alignments:
		alignments = dict((w,w) for w in tree1.leaves())
	def ideq(tree1, tree2):
		# test if tree1 and tree2 are equal, but only compare IDs if 
		# nodes have them, so that lemmatized subtrees are recognized as equivalent.
		if len(tree1) == len(tree2):
			if isinstance(tree1, Tree) and isinstance(tree2, Tree):
				if (tree1.node.split("@")[-1] == tree2.node.split("@")[-1]
					or (tree1.node.split("!")[0] in ('s', 'sq', 'S', 'SQ')
					and tree2.node.split("!")[0] in ('s', 'sq', 'S', 'SQ'))):
					return "@" in tree1.node or all(ideq(a,b) for a,b in zip(tree1, tree2))
				else: return False
			else: return isinstance(tree1, str) and isinstance(tree2, str) and tree1.lower() == tree2.lower()
		else: return False
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
				#if i == j and isinstance(i, Tree):
				if isinstance(i, Tree) and ideq(i, j):
					# check if larger than current maximal tree, etc.
					if len(leaves_and_frontier_nodes(i)) > max_shared_subtree_size:
						max_shared_subtree_size = len(leaves_and_frontier_nodes(i))
						max_shared_subtree = (i, j, parent1, num1, parent2, num2)

		# If no subtree is found yet, find an 'almost-match' (e.g. a
		# conjugation)
		if USE_LEMMATIZATION and max_shared_subtree == None:
			for (parent1, num1, i) in my_subtrees(tree1):
				if isinstance(i, Tree) and len(i) == 1 and type(i[0]) == str:
					for (parent2, num2, j) in my_subtrees(tree2):
						if isinstance(j, Tree) and	len(j) == 1 and type(j[0]) == str:
							# verbs are handled by the wordnet lemmatizer,
							# handle contractions as special cases.
							if ((((i.node[0] in 'vV' and j.node[0] in 'vV') or
								(i.node in ('md', 'MD') and j.node in ('md','MD')))
							and (wnl.lemmatize(i[0], 'v') == wnl.lemmatize(j[0], 'v')
							or (i[0] in ("is", "'s") and j[0] in ("is", "'s") and i[0] != j[0])))
							or (i[0] in ("not", "n't") and j[0] in ("not", "n't") and i[0] != j[0])):
								# if word is the same it's probably a tagging error:
								if i[0] == j[0]:
									pass
									# this leads to overgeneralization
									#i.node = j.node
									#print "corrected tag", j.node, "=>", i.node
								else: print "lemmatized", i[0], "<=>", j[0]
								lemmatized_equivalents = (i, j, parent1, num1, parent2, num2)
							# also do any <=> some

		# Remove the shared subtree from the tree...
		if max_shared_subtree:
			(i, j, parent1, num1, parent2, num2) = max_shared_subtree
			# Decorate tree with ids.
			if decorate: i, j = decorate_with_ids(i, j)
			parent1[num1] = Tree(i.node, []) # tree.node
			parent2[num2] = Tree(j.node, []) # tree.node
		elif lemmatized_equivalents:
			(i, j, parent1, num1, parent2, num2) = lemmatized_equivalents
			if decorate: i, j = decorate_pair(i, j)
			parent1[num1] = Tree(i.node, [])
			parent2[num2] = Tree(j.node, [])
		
		if lemmatized_equivalents:
			equivalents.append((i, j))
		elif max_shared_subtree == None:
			shared_subtrees = False
		else:
			linked_subtrees.append((i, j))
	# Decompose linked subtrees into minimal subtrees (so far: these always are
	# PCFG-rules)
	minimal_subtrees = []
	for a,b in linked_subtrees:
		for i,j in zip(a.productions(), b.productions()):
			if len(i.rhs()) > 0:
				minimal_subtrees.append(
					(production_to_tree(i), production_to_tree(j)))
	minimal_subtrees.extend(equivalents)

	minimal_subtrees.append((tree1, tree2))
	return minimal_subtrees

def linked_subtrees_to_probabilistic_rules(linked_subtrees, limit_subtrees=1000):
	def myindex(l, x):
		# only match ID, not label
		for n, a in enumerate(l):
			if x in a.node: return n
		raise ValueError("myindex(x): x not in list")
	# Add 'links' between leaf nodes.
	print "Phase 1..."
	linked_subtrees2 = []
	for t1, t2 in linked_subtrees:
		l1 = filter(lambda x: (isinstance(x, Tree) and '@' in x.node), leaves_and_frontier_nodes(t1))
		l2 = filter(lambda x: (isinstance(x, Tree) and '@' in x.node), leaves_and_frontier_nodes(t2))
		# Very ugly, but might be needed to guarantee the right outcome...
		a = [(l1.index(x), myindex(l2, x.node.split("@")[1])) for x in l1]
		# a.sort()	# ???!?
		a = [x[1] for x in a] 
		linked_subtrees2.append((t1, t2, a))
		#t1.freeze()
		#t2.freeze()
	print "Phase 2..."
	# For every addressed node, look at possible ways to remove id again.
	# Find addressed leaf-positions
	# Add frequency counts
	newtrees = []
	for (t1, t2, links) in linked_subtrees2:
		print t1, t2, links
		leafindex1 = dict(frontier_nodes(t1))
		leafindex2 = dict((a.split("@")[-1], b) for a,b in frontier_nodes(t2))
		# note: a.split("@")[-1] either gives the ID if there is one, or returns the whole string (in case of a leaf)
		indices12 = [(leafindex1[l], leafindex2[l.split("@")[-1]], l) for l in leafindex1.keys() if l.split("@")[-1] in leafindex2]
		for n, a in enumerate(sublists(indices12)):
			if limit_subtrees and n > limit_subtrees: break
			#print "sublist...", a
			leaves = [str(b[2]) for b in indices12 if b not in a]
			newtree1 = t1.copy(True)
			newtree2 = t2.copy(True)
			for (l, r, leaf) in a:
				newtree1[l].node = rmid(newtree1[l].node)
				newtree2[r].node = rmid(newtree2[r].node)
			newtrees.append((newtree1, newtree2, links,
				reduce(mul, (count(leaf, linked_subtrees) for leaf in leaves), 1)))
			if "@" in newtree1.node:
				newtree1a = newtree1.copy(True)
				newtree2a = newtree2.copy(True)
				newtree1a.node = rmid(newtree1.node)
				newtree2a.node = rmid(newtree2.node)
				newtrees.append((newtree1a, newtree2a, links,
					reduce(mul, (count(leaf, linked_subtrees) for leaf in leaves), 1)) )
	return newtrees
		
def munge(deriv, tree, notcovered):
	# deriv is a translation using a partial match, tree is the original tree,
	# notcovered is a list of indices from tree that were not part of the partial match
	# reinsert all constituents from the original tree that were not present in the partial match
	# the challenge is to find the right constituent and index to insert at
	deriv = Tree.convert(deriv)
	# clean up derivation, remove any parts without yield
	tp = deriv.treepositions()
	while tp:
		idx = tp.pop(0)
		if isinstance(deriv[idx], Tree) and deriv[idx].leaves() == []:
			del deriv[idx]
			tp = deriv.treepositions()
	while notcovered:
		nc = notcovered[0]
		# skip frontier nodes or terminals
		indices = [a for a in deriv.treepositions() if isinstance(deriv[a], Tree) and deriv[a]]
		indices.sort(key=len)
		nodes = [deriv[a].node for a in indices]
		# linked nodes would be better
		# try to find its former parent
		idx = None
		parent = tree[nc[:-1]].node
		if len(nc) == 2 and parent == "s": parent = "sq"
		elif len(nc) == 2 and parent == "sq": parent = "s"
		if parent in nodes and len(nc) - 1 == len(indices[nodes.index(parent)]):
			idx = indices[nodes.index(parent)]
		elif any(x.node in nodes for x in tree[nc[:-1]]):
			# put it in a constituent that has a sibling of this node
			siblings = [y.node for y in tree[nc[:-1]]]
			tmp = FreqDist(x[:-1] for x in indices if deriv[x].node in siblings)
			idx = [a for a in tmp if len(a) <= len(nc)]
			if idx: idx = idx.pop()
		if idx == None:
			# try to append it to parent. 
			# otherwise, attach to root
			for n in range(1, len(nc)):
				parent = tree[nc[:-n]].node
				if len(nc[:-n]) == 1 and parent == "s": parent = "sq"
				elif len(nc[:-n]) == 1 and parent == "sq": parent = "s"
				if parent in nodes and len(nc) - n == len(indices[nodes.index(parent)]):
					idx = indices[nodes.index(parent)]
					break
				else: idx = ()
		if idx: deriv[idx] = Tree.convert(guessorder(deriv[idx], tree, nc))
		else: deriv = Tree.convert(guessorder(deriv[idx], tree, nc))
		# remove this node and all of its children as we've covered them now
		notcovered = [x for x in notcovered if x[:len(nc)] != nc]
	return deriv
def guessorder(deriv, tree, notcovered):
	def partition(list, middle):
		for n in range(len(list)):
			if list[n:n+len(middle)] == middle:
				return list[:n], list[n+len(middle):]
		raise ValueError("middle not in list")
	#guess proper order
	left, right = partition([a for a,b in tree.pos()], [a for a,b in tree[notcovered].pos()])
	leftp, rightp = partition([b for a,b in tree.pos()], [b for a,b in tree[notcovered].pos()])
	positions = []
	for n in range(len(deriv)+1):
		dleft = chain(*(x.pos() for x in deriv[:n] if isinstance(x, Tree)))
		dright = chain(*(x.pos() for x in deriv[n:] if isinstance(x, Tree)))
		# match on words, backoff to POS tags only if word is not found
		positions.append((sum(1 for a,b in dleft if a in left or (a not in right and b in leftp)) 
				+ sum(1 for a,b in dright if a in right or (a not in left and b in rightp)),
				#min(notcovered[-1], n) - max(notcovered[-1], n),
				n))
		# how to break a tie? idea: generate both..
		# currently: pick index closest to original index

	deriv.insert(max(positions, #key=lambda x: x[0]
		)[-1], tree[notcovered])
	#print tree[notcovered].node, "=>", deriv.node, "positions", positions
	return deriv

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

#@memoize
def count(our_node, linked_subtrees):
	for a, b in linked_subtrees:
		if a.node == our_node:
			return reduce(mul, (count(c, linked_subtrees) + 1 for
				c in set(x for x,y in frontier_nodes(a))), 1)
	#raise ValueError("node %s not found in linked subtrees" % our_node)
	return 0 # -1 ??

def frontier_nodes(tree):
	if frontier_node(tree):
		return [(tree.node, ())]
	elif type(tree) == str:
		return []
	else:
		#return reduce(chain, ([(fnode, (pos,) + r) for (fnode, r) in frontier_nodes(stree)] for pos, stree in enumerate(tree)))
		fnodes = []
		for pos, stree in enumerate(tree):
			#fnodes += [(fnode, ((pos,) + r)) for (fnode, r) in frontier_nodes(stree)]
			fnodes += [(fnode, (pos,) + r) for (fnode, r) in frontier_nodes(stree)]
		return fnodes

#def frontier_nodes(tree):
#	return dict((l, p) for l, p
#		in zip(tree.leaves(), tree.treepositions('leaves')) if '@' in l)

def frontier_node(tree):
	return isinstance(tree, Tree) and len(tree) == 0

def comb(n):
	result = 0
	for x in range(1, n+1):
		result += reduce(mul, range(1, n+1), 1) / (reduce(mul, range(1, x+1), 1) * reduce(mul, range(1, n-x+1), 1))
	return result

def sublists(l):
	# ordered from big to small:
	return chain( ((),), reduce(chain, (combinations(l, a) for a in range(len(l), 0, -1)), ()))
	# ordered from small to big:
	#return reduce(chain, (combinations(l, a) for a in range(len(l) + 1)))

def rmid(x):
	return x.split("@")[0]

def decorate_with_ids(tree1, tree2):
	global current_id
	utree1 = tree1.copy(True)
	utree2 = tree2.copy(True)
	for a, b in zip(utree1.subtrees(), utree2.subtrees()):
		if not ("@" in a.node):		# ????!
			a.node = "%s@%d" % (a.node, current_id)
			b.node = "%s@%d" % (b.node, current_id)
			current_id += 1
	return utree1, utree2

def undecorate_with_ids(tree):
	tree = Tree.convert(tree)
	for a in tree.subtrees(filter=lambda x: '@' in x.node):
		a.node = a.node[:a.node.index("@")]
	return tree

def decorate_pair(tree1, tree2):
	global current_id
	utree1 = tree1.copy(True)
	utree2 = tree2.copy(True)
	utree1.node = "%s@%d" % (utree1.node, current_id)
	utree2.node = "%s@%d" % (utree2.node, current_id)
	current_id += 1
	return utree1, utree2

def treeify(node):
	if type(node) == Nonterminal:
		return Tree(str(node), [])
	else:
		return node
	
def production_to_tree(production):
	return Tree(str(production.lhs()), [treeify(r) for r in production.rhs()])

def my_subtrees(tree): 
	for n, child in enumerate(tree): 
		yield tree, n, child
		if isinstance(child, Tree): 
			for subtree in my_subtrees(child): 
				yield subtree

def test():
	tree1 = Tree("(S (NP John) (VP (V bought) (NP (DET a) (N car))))")
	tree2 = Tree("(S (VBZ did) (NP John) (VP (V buy) (NP (DET a) (N car))))")
	t = minimal_linked_subtrees(tree1, tree2)
	for a,b in t: print a,b
	t2 = linked_subtrees_to_probabilistic_rules(t)
	print
	print
	for b in t2:
		for c in b: print c
		print
	gr = TransformationDOP()
	gr.add_to_grammar(t2)
	gr.print_grammar()
	a = gr.get_grammar()
	return a

def test2():
	tree1 = Tree("(TOP (SQ (VBD Did) (NP (PRP I)) (VP (VB buy) (NP (PRP it))) (. ?)))")
	tree2 = Tree("(TOP (S (NP (PRP I)) (VP (VBD bought) (NP (PRP it))) (. .)))")
	t = minimal_linked_subtrees(tree1, tree2)
	print "\nminimal linked subtrees"
	for a,b in t: print a,b
	print "end\n"
	t2 = linked_subtrees_to_probabilistic_rules(t)
	print "\nlinked subtrees to probabilistic rules"
	for b in t2:
		for c in b: print c
		print
	tdop = TransformationDOP()
	tdop.add_to_grammar(t2)
	tdop.sort_grammar()
	print "DOT grammar"
	tdop.print_grammar()
	tree = Tree("(TOP Did (NP (NNP Mr.) (NNP Freeman)) (VP (VB have) (NP (NP (VB notice)) (PP (IN of) (NP (DT this))))) ?)")
	tree1 = Tree("(TOP (SQ (VBD Did) (NP (NNP Mr.) (NNP Freeman)) (VP (VB have) (NP (NP (VB notice)) (PP (IN of) (NP (DT this))))) (. ?)))")
	tdop.extendlex([(tree1, tree1)])
	parser = ViterbiParser(tdop.get_grammar(root="TOP"))
	print "1"
	t,p = tdop.get_mlt_deriv(tree, smoothing=True)
	print parser.grammar()
	print p, t
	try:
		t,p = tdop.get_mlt_deriv(parser.parse("Did Mr. Freeman have notice of this ?".split()), smoothing=True)
		print p, t
	except Exception as e:
		print e
	print "2"
	tree = Tree("(TOP (SQ (VBD Did) (NP (NNP Mr.) (NNP Freeman)) (VP (VB have) (NP (NP (VB notice)) (PP (IN of) (NP (DT this))))) (. ?)))")
	for t,p in sorted(list(tdop.my_mlt_deriv(tree1)), key=lambda x: x[1]):
		print p, t
	parser = ViterbiParser(tdop.get_my_grammar(root="TOP"))
	print parser.grammar()
	try:
		tree1 = parser.parse("Did Mr. Freeman have notice of this ?".split())
		for t,p in sorted(list(tdop.my_mlt_deriv(tree1)), key=lambda x: x[1]):
			print p, t
	except Exception as e:
		print e
	

def forcepos(tree):
	""" make sure all terminals have POS tags; 
	invent one if necessary ("parent_word") """
	result = tree.copy(True)
	for a in tree.treepositions('leaves'):
		if len(tree[a[:-1]]) != 1:
			result[a] = Tree("%s_%s" % (tree[a[:-1]].node, tree[a]), [tree[a]])
	return result

def removeforcepos(tree):
	""" removed forced POS tags of the form "parent_word" """
	result = tree.copy(True)
	for a in tree.treepositions('leaves'):
		if "_" in tree[a[:-1]].node:
			result[a[:-1]] = tree[a]
	return result

def remcnfmarks(tree):
	for a in tree.subtrees(filter=lambda x: '!<>' in x.node):
		a.node = a.node.replace('!<>', '')
def foldlabels(tree, all=False):
	if all: exclude = ["top"]
	else: exclude = "top s sq sinv smain vp np".split()
	for a in tree.subtrees(filter=lambda x: x.height() > 2 and x.node.lower() not in exclude):
		a.node = "X"
def mark_be_do(tree, vbdepth=3):
	if tree[0].node.lower() in ("s", "sinv"): tree[0].node = "Smain"	
	for a in tree.treepositions():
		if isinstance(tree[a], Tree) and tree[a].height() == 2: 
			preterminal = tree[a]
			if preterminal.node.lower() == "md" and len(a) == vbdepth:
					tree[a[:-1]].node += "-aux"
			if preterminal.node.lower() in "vb vbz vbd vbp".split():
				if wnl.lemmatize(preterminal[0].lower(), "v") == "be" and len(a) == vbdepth:
					preterminal.node += "-aux"
					tree[a[:-1]].node += "-aux"
				elif wnl.lemmatize(preterminal[0].lower(), "v") == "have" and len(a) == vbdepth:
					preterminal.node += "-aux"
					tree[a[:-1]].node += "-aux"
				elif wnl.lemmatize(preterminal[0].lower(), "v") == "do" and len(a) == 2:
					preterminal.node += "-do"

def interface():
	corpus = """(S (NP John) (VP (V bought) (NP (DT a) (N car))))
	(S (VP (VBZ did)) (NP John) (VP (V buy) (NP (DT a) (N car))))
	(S (NP Mary) (VP (VBZ is) (ADJP (JJ happy))))
	(S (VBZ is) (NP Mary) (ADJP (JJ happy)))
	(S (NP (NP (DT the) (NN man)) (SBAR (WHNP (WP who)) (S (VP (VBZ is) (VP (VBG talking)))))) (VP (VBZ is) (VP (VBG walking))))
	(S (VBZ is) (NP (NP (DT the) (NN man)) (SBAR (WHNP (WP who)) (S (VP (VBZ is) (VP (VBG talking)))))) (VP (VBG walking)))"""
	corpus = """(S (NP Mary) (VP (VBZ is) (ADJP (JJ happy))))
	(S (VBZ is) (NP Mary) (ADJP (JJ happy)))
	(S (NP (NP John) (SBAR (WHNP (WP who)) (S (VP (VBZ mumbles))))) (VP (VBZ dreams) (PP (IN about) (NP unicorns))))
	(S (VBZ Does) (NP (NP John) (SBAR (WHNP (WP who)) (S (VP (VBZ mumbles))))) (VP (VB dream) (PP (IN about) (NP unicorns))))"""
	#(S (NP (NP John) (SBAR (WHNP (WP who)) (S (VP (VBZ is) (VP (VBG sleeping)))))) (VP (VBZ dreams) (PP (IN about) (NP unicorns))))
	#(S (VBZ Does) (NP (NP John) (SBAR (WHNP (WP who)) (S (VP (VBZ is) (VP (VBG sleeping)))))) (VP (VB dream) (PP (IN about) (NP unicorns))))"""
	corpus = map(Tree, corpus.lower().splitlines())
	corpus = zip(corpus[::2], corpus[1::2])
	print 'corpus:'
	for a,b in corpus: print "< %s, %s  >" % (str(a), str(b))
	
	tdop = TransformationDOP()
	for tree1, tree2 in corpus:
		m = minimal_linked_subtrees(tree2, tree1)
		l = linked_subtrees_to_probabilistic_rules(m)
		tdop.add_to_grammar(l)
		tdop.add_to_grammar(linked_subtrees_to_probabilistic_rules(minimal_linked_subtrees(tree1, tree2)))
	tdop.sort_grammar()
	#parser = ViterbiParser(tdop.get_grammar(root="s"))
	grammar, lexicon = tdop.get_grammar(bitpar=True)
	parser = BitParChartParser(grammar, lexicon, rootsymbol="s", n=1000)
	grammar = tdop.get_my_grammar(root="s")
	myparser = ViterbiParser(grammar)
	print 'done'
	#basic REPL
	while True:
		print 'sentence:',
		a=raw_input()
		parsetree = None
		myparsetree = None
		#tree, prob = topdownparse(grammar._productions, a.split(), root="s")
		#for n, result in enumerate(mytopdownparse(grammar, a.split(), t=Tree("s",[]))):
		#	if n > 3: break
		#	print "top down", result[0], result[1]
		try:
			parsetree = removeforcepos(list(parser.nbest_parse(a.split()))[0])
			parsetree.un_chomsky_normal_form()
			print "viterbi1:", parsetree
		except Exception as e:
			print e
		try:
			myparsetree = myparser.parse(a.split())
			print "viterbi2:", myparsetree
		except Exception as e:
			print e
		try:
			for transformed, prob in tdop.get_mlt_deriv_multi(parsetree, smoothing=False):
				print "transformed1 (prob=%s): %s" % (repr(prob), transformed)
				print "words:", " ".join(transformed.leaves())
		except Exception as e:
			print e
		if myparsetree in (None, []): continue
		for transformed, prob in list(tdop.my_mlt_deriv(myparsetree, allowpartial=True)):
			print "transformed2 (prob=%s): %s" % (repr(prob), transformed)
			print "words:", " ".join(transformed.leaves())

def run(tdop, sentsortrees, gold, resultsfile, trees=False, my=False, bootstrap=False):
	if not trees:
		#parser = ViterbiParser(tdop.get_grammar(root="top"))
		if my:
			rules, lexicon = tdop.get_my_grammar(bitpar=True)
		else:
			rules, lexicon = tdop.get_grammar(bitpar=True, freqfn=sum)
		parser = BitParChartParser(rules, lexicon, cleanup=True, rootsymbol="top", n=100)
		print 'grammar done'
	results = []
	resultfds = []
	noparse = 0
	for n, a in enumerate(sentsortrees):
		if trees:
			print n, "source:", " ".join(a.leaves())
			parsetrees = {a.freeze() : 1}
		else:
			print n, "source:", a
			try:
				parsetrees1 = list(parser.nbest_parse(a.split()))
			except Exception as e:
				parsetrees1 = []
				print n, "parsing failed", e
			parsetrees = FreqDist()
			for b in parsetrees1: 
				b.un_chomsky_normal_form()
				parsetrees.inc(ImmutableTree.convert(removeforcepos(b)), count=b.prob())
			print "parsetrees:", len(parsetrees)
			if len(parsetrees) == 0: noparse += 1
		resultfd = FreqDist()
		t = 0
		for m, b in enumerate(parsetrees):
			if my:
				for nn, (result, prob) in enumerate(tdop.my_mlt_deriv(b)):
					resultfd.inc(" ".join(result.leaves()), count=parsetrees[b] * prob)
					t += 1
					if nn > 1000: break
				#if resultfd: break # skip other parse trees
				if False: pass
				else:
					print "trying partial"
					for nn, (result, prob) in enumerate(tdop.my_mlt_deriv(b, allowpartial=True)):
						t += 1
						resultfd.inc(" ".join(result.leaves()), count=parsetrees[b] * prob)
						if nn > 1000: break
				continue
			for nn, (result, prob) in enumerate(tdop.get_mlt_deriv_multi(b, smoothing=True, verbose=False)):
				# count number of addressed nodes; the more addressed nodes, the shorter the derivation is
				if result:
					if bootstrap:
						resultfd.inc(undecorate_with_ids(result).freeze(), count=parsetrees[b] * prob or 1e-200)
					else:
						if m == nn == 0: print parsetrees[b], b, "\n =>", prob, result
						resultfd.inc((undecorate_with_ids(result).freeze(), 
									sum(1 for a in result.subtrees() if "@" in a.node)), 
									count=log(parsetrees[b]) + prob) # or 1e-200)
					t += 1
				if nn > 100: break
		if not trees and not resultfd and parsetrees and undecorate_with_ids(parsetrees.keys()[0]).freeze() not in parsetrees:
			for nn, (result, prob) in enumerate(tdop.get_mlt_deriv_multi(undecorate_with_ids(parsetrees.keys()[0]), smoothing=True, verbose=False)):
				if result and undecorate_with_ids(result).freeze() not in resultfd:
					if bootstrap:
						resultfd.inc(undecorate_with_ids(result).freeze(), count=parsetrees[b] * prob or 1e-200)
					else:
						resultfd.inc((undecorate_with_ids(result).freeze(), 
								sum(1 for a in result.subtrees() if "@" in a.node)), 
								count=log(parsetrees[b]) + prob) # or 1e-200)
					t += 1
				if nn > 100: break
		print "transformations: ", t
		if not trees and resultfd:
			# order the shortest derivations by probability:
			if bootstrap:
				pass
				#resultfd = FreqDist(dict((tree, prob) for (tree, n), prob in resultfd.items() if n == m))
			else:
				m = max(y for x,y in resultfd)
				print len(resultfd), m,
				newfd = FreqDist()
				for (tree, mm), prob in resultfd.items():
					#if mm == m:
					newfd.inc(tree, prob)
				resultfd = newfd
				#resultfd = FreqDist(dict((" ".join(tree.leaves()), prob) for (tree, n), prob in resultfd.items() if n == m))
				print len(resultfd)
		def words(tree):
			return " ".join(tree.leaves())
		if parsetrees and resultfd:
			results.append("\n".join("%d. [p=%s] %s" % (n, repr(prob), words(tree)) for tree, prob in resultfd.items()) + "\n")
			print results[-1]
		else:
			if parsetrees and not trees: results.append("not transformed: %s\n" % a)
			elif not parsetrees and not trees: results.append("not parsed: %s\n" % a)
		resultfds.append(resultfd)
	print "done"
	def lem(sent):
		def f(a):
			if a == "n't": return "not"
			if a == "'s": return "is"
			return a
		if sent: return tuple([wnl.lemmatize(f(a), "v") for a in sent])
		else: return sent

	def fmax(a):
		# FreqDist's max() method doesn't work for negative values
		if a: return max(a.items(), key=lambda (k,v): v)[0]
	if bootstrap:
		def strtree(a):
			if a and fmax(a): return fmax(a)._pprint_flat("","()",0) + "\n"
			else: return "\n"
		def strtrees(a):
			if a: return "\n".join(x._pprint_flat("","()",0) for x in a if x) + "\n\n"
			else: return "\n\n"
		open(resultsfile, "w").writelines(map(strtree, resultfds))
		open(resultsfile+"all", "w").writelines(map(strtrees, resultfds))
		return

	lgold = [lem(a.lower().split()) for a in gold]
	a,b = 0,0
	dist = []
	dist1 = []
	wrong = []
	for n, (fd, sent) in enumerate(zip(resultfds, lgold)):
		if fmax(fd):
			if lem(words(fmax(fd)).lower().split()) == sent:
				a += 1
			else:
				wrong.append(n)
		if sent in (lem(words(x).lower().split()) for x in fd.keys()): b += 1
		if fmax(fd): 
			dist.append(min(edit_distance(sent, lem(words(x).split())) for x in fd))
			dist1.append(edit_distance(sent, lem(words(fmax(fd)).split())))
		else: 
			dist.append(len(sent))
			dist1.append(len(sent))
	exactcnt = sum(1 for a,b in zip(resultfds, gold) if a and words(fmax(a)) == b)
	stats = (
	"exact match:        %d of %d => %.2f %%\n"
	"match ranked first: %d of %d => %.2f %%\n" 
	"match of any rank:  %d of %d => %.2f %%\n" 
	"f-measure: %.2f\n" 
	"precision: %.2f\n" 
	"recall: %.2f\n" 
	"average edit distance (of best matches): %.2f\n" 
	"sentences with edit distance < 1: %s\n"
	"distances of first matches: %s\n"
	"distances of best matches:  %s\n"
	"indices of mistakes: %s\n" % (
			exactcnt, len(gold), float(exactcnt) / len(gold) * 100,
			a, len(gold), float(a) / len(gold) * 100, 
			b, len(gold), float(b) / len(gold) * 100, 
			f_measure(set(lgold), set(lem(words(fmax(x)).lower().split()) for x in resultfds if fmax(x))),
			precision(set(lgold), set(lem(words(fmax(x)).lower().split()) for x in resultfds if fmax(x))),
			recall(set(lgold), set(lem(words(fmax(x)).lower().split()) for x in resultfds if fmax(x))), 
			mean(dist), sum(1 for x in dist1 if x <= 1), 
			repr(dist1), repr(dist), repr(wrong)))
	if not trees:
		stats += "sentences with no parse: %d\n" % noparse
	stats += "sentences with no transformation: %d\n" % sum(1 for x in resultfds if not x)
	print stats
	results.append(stats)
	open(resultsfile, "w").writelines(results)
	stats = {"exact match:" : float(exactcnt) / len(gold) * 100,
	"match ranked first:" : float(a) / len(gold) * 100,
	"match of any rank:" : float(b) / len(gold) * 100,
	"f-measure:" : f_measure(set(lgold), set(lem(words(fmax(x)).lower().split()) for x in resultfds if fmax(x))) or 0.0,
	"precision:" : precision(set(lgold), set(lem(words(fmax(x)).lower().split()) for x in resultfds if fmax(x))) or 0.0,
	"recall:" : recall(set(lgold), set(lem(words(fmax(x)).lower().split()) for x in resultfds if fmax(x))) or 0.0,
	"average edit distance (of best matches):" : mean(dist),
	"sentences with edit distance < 1:" : sum(1 for x in dist1 if x <= 1),
	"sentences with no parse:" : noparse,
	"sentences with no transformation:" : sum(1 for x in resultfds if not x) }
	return stats

def runexp():
	import cPickle
	global CHECK_SUBSTITUTION
	sentsinter = open("corpus/sentences-interr3.txt").read().lower().splitlines()
	sentsdecl = open("corpus/sentences-decl3.txt").read().lower().splitlines()
	treesinter = map(lambda x: Tree(x.lower()), open("corpus/trees-interr3.txt"))
	treesdecl = map(lambda x: Tree(x.lower()), open("corpus/trees-decl3.txt"))
	newsentsinter = open("corpus/sentences-interr1.txt").read().lower().splitlines()
	newsentsdecl = open("corpus/sentences-decl1.txt").read().lower().splitlines()
	newtreesdecl = map(lambda x: Tree(x.lower()), open("corpus/trees-decl1.txt"))
	newtreesinter = map(lambda x: Tree(x.lower()), open("corpus/trees-interr1.txt"))

	newtrees = map(lambda x: Tree(x.lower()), open("corpus/trees-decl4.txt"))
	trees_tdop_parsed = map(lambda x: undecorate_with_ids(Tree(x.lower())), open("trees.txt"))

	corpus = list(zip(newtreesdecl + treesdecl, newtreesinter + treesinter))
	rightcorpus = []
	#corpus = list(zip(newtreesdecl, newtreesinter))
	for a, b in corpus:
		#foldlabels(a, all=True); foldlabels(b, all=True)
		foldlabels(a, all=False); foldlabels(b, all=False)
		#mark_be_do(a); mark_be_do(b, 3)
		#a1,b1 = a.copy(True), b.copy(True)
		# use a different separator so as not to interfere with the
		# binarization performed at the PCFG level for bitpar in tdop.get_grammar()
		#a.chomsky_normal_form(factor='left', horzMarkov=0, childChar="!")
		#b.chomsky_normal_form(factor='left', horzMarkov=0, childChar="!")
		#a1.chomsky_normal_form(factor='right', horzMarkov=0, childChar="!")
		#b1.chomsky_normal_form(factor='right', horzMarkov=0, childChar="!")
		#remcnfmarks(a); remcnfmarks(b); remcnfmarks(a1); remcnfmarks(b1)
		#rightcorpus.append((a1, b1))
	newtreesright = []
	for a in newtrees:
		#foldlabels(a) #; foldlabels(b)
		#mark_be_do(a) #; mark_be_do(b)
		a1 = a.copy(True)
		a.chomsky_normal_form(factor='left', horzMarkov=0, childChar="!")
		a1.chomsky_normal_form(factor='right', horzMarkov=0, childChar="!")
		newtreesright.append(a1)
		#remcnfmarks(a) #; remcnfmarks(b)

	train = True
	mlsts = []
	if train:
		tdop = TransformationDOP()
		for n, (tree1, tree2) in enumerate(corpus[:-20] + rightcorpus[:-20]):
			print n
			#minl = minimal_linked_subtrees(tree1, tree2)
			#pos = dict(tree2.pos())
			#for w,p in tree1.pos():
			#	if w in pos and pos[w] != p:
			#		print "%d. (%s %s) != (%s %s)" % (n, p, w, pos[w], w)
			#		print minl[-1][0], minl[-1][1]
			#mlsts.append((n, minl[-1], (tree1, tree2), str(minl[-1][0]).count("@"), len(list(minl[-1][0].subtrees())) - 3))
			tdop.add_to_grammar(
				linked_subtrees_to_probabilistic_rules(
				minimal_linked_subtrees(tree2, tree1), limit_subtrees=1000))

		#for n, (tree1, tree2) in enumerate(zip(newtrees+newtreesright, newtrees+newtreesright), n+1):
		#	print "newtree", n
		#	tdop.add_to_grammar(
		#		linked_subtrees_to_probabilistic_rules(
		#		filter(lambda x: x[0].node.lower().split("@")[0] not in "top s sq vp TOP S SQ VP".split(), minimal_linked_subtrees(tree1, tree2)), limit_subtrees=1000))
		# this code shows the pairs of exemplars with the least links:
		mlsts.sort(key=lambda x: x[4] - x[3])
		x = 0
		for a,(b1,c1), (b,c),d,e in mlsts:
			if e - d > 1:
				print "%d. %d / %d = %f" % (a, d, e, d/float(e))
				print b1
				print c1
				x += 1
				#print b
				#print c
		#print sum(x[3] for x in mlsts), "/", sum(x[4] for x in mlsts), "=", sum(x[3] for x in mlsts) / float(sum(x[4] for x in mlsts))
		print x
		#return
		tdop.extendlex(zip(treesinter, treesdecl)[-20:])
		#tdop.extendlex(zip(newtrees, newtrees))
		print "training done" 
	else:
		#tdop = cPickle.load(open("tdop.pickle","rb"))
		pass
	
	#run(tdop, trees_tdop_parsed, "results0.txt", getpos=zip(treesinter, treesdecl)[-20:], trees=True)
	#run(tdop, sentsdecl[-20:], sentsinter[-20:], "results1.txt")
	#run(tdop, s, sd, "results1.txt")
	#CHECK_SUBSTITUTION = False
	#print "CHECK_SUBSTITUTION", CHECK_SUBSTITUTION
	#run(tdop, sentsinter[-20:], sentsdecl[-20:], "results1.txt")

	CHECK_SUBSTITUTION = True
	print "CHECK_SUBSTITUTION", CHECK_SUBSTITUTION
	#run(tdop, [" ".join(a.leaves()) for a in newtrees], [], "trees-inter4.txt", bootstrap=True)
	run(tdop, sentsinter[-20:], sentsdecl[-20:], "results1.txt")
	#tdop.sort_grammar(withids=False)
	#run(tdop, treesinter[-20:], sentsdecl[-20:], "results2.txt", trees=True, my=True)
	#run(tdop, treesdecl[-20:], sentsinter[-20:], "results2.txt", trees=True, my=True)
	#cPickle.dump(tdop.mangled, open("mangled.pickle","wb"), 1)
	#tdop.sort_grammar(True)
	#run(tdop, sentsinter[-20:], sentsdecl[-20:], "results3.txt", my=True)
	#run(tdop, newtreesdecl, newsentsinter, "results5.txt", trees=True, my=True)
	print "testing done"
	#if train: cPickle.dump(tdop, open("tdop.pickle","wb"), 1)

def preprocess(trees, options):
	additionaltrees = []
	for a in trees:
		if a[0].node.lower() == "sq": verbdepth=3
		else: verbdepth = 2
		if 'foldmost' in options: foldlabels(a)
		elif 'foldall' in options: foldlabels(a, all=True)
		if 'markaux' in options: mark_be_do(a, verbdepth)
		if 'rightbranching' in options: a.chomsky_normal_form(factor='right', horzMarkov=0, childChar="!")
		elif 'leftbranching' in options: a.chomsky_normal_form(factor='left', horzMarkov=0, childChar="!")
		elif 'bothbranching' in options:
			b = a.copy(True)
			a.chomsky_normal_form(factor='left', horzMarkov=0, childChar="!")
			b.chomsky_normal_form(factor='right', horzMarkov=0, childChar="!")
			additionaltrees.append(b)
		if 'stripcnfmarks' in options: 
			remcnfmarks(a)
			if 'bothbranching' in options: remcnfmarks(additionaltrees[-1])
	return additionaltrees
	
def tenfold():
	# first corpus
	sentsinter = open("corpus/sentences-interr3.txt").read().lower().splitlines()
	sentsdecl = open("corpus/sentences-decl3.txt").read().lower().splitlines()
	treesinter = map(lambda x: Tree(x.lower()), open("corpus/trees-interr3.txt"))
	treesdecl = map(lambda x: Tree(x.lower()), open("corpus/trees-decl3.txt"))
	# second corpus
	sentsinter += open("corpus/sentences-interr1.txt").read().lower().splitlines()
	sentsdecl += open("corpus/sentences-decl1.txt").read().lower().splitlines()
	treesdecl += map(lambda x: Tree(x.lower()), open("corpus/trees-decl1.txt"))
	treesinter += map(lambda x: Tree(x.lower()), open("corpus/trees-interr1.txt"))
	
	#treesdecl = map(lambda x: Tree(x.lower()), open("corpus/filtered-decl.txt"))
	#treesinter = map(lambda x: Tree(x.lower()), open("corpus/filtered-inter.txt"))
	#sentsdecl = map(lambda x: " ".join(x.leaves()), treesdecl)
	#sentsinter = map(lambda x: " ".join(x.leaves()), treesinter)
	filtered = [2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 18, 19, 20, 21, 22, 23, 24, 26, 30, 31, 32, 34, 35, 36, 37, 40, 43, 50, 53, 54, 59, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 72, 73, 74, 75, 77, 80, 81, 84, 87, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 100, 101, 102, 103, 104, 105, 106, 108, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 123, 124, 127, 128, 129, 130, 131, 132, 133, 135, 136, 137, 138, 139, 141, 142, 143, 144, 145, 146, 147, 149, 151, 152, 153, 154, 155, 156, 158, 160, 161, 162, 163, 165, 166, 167, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]

	parameters = ( ('foldmost', 'foldall', 'nofold'), ('markaux', 'nomarks'), 
				('rightbranching', 'leftbranching', 'bothbranching', 'nobinarization'), 
				('stripcnfmarks', 'cnfmarks') )
	parameters = filter(lambda x: 'nobinarization' not in x or 'cnfmarks' in x, product(*parameters))
	parameters = (tuple("foldmost nomarks rightbranching cnfmarks".split()),
			tuple("foldall markaux rightbranching cnfmarks".split()))
	proccorpus = {}
	for param in parameters:
		decl = [a.copy(True) for a in treesdecl]
		inter = [a.copy(True) for a in treesinter]
		rdecl = preprocess(decl, param)
		rinter = preprocess(inter, param)
		proccorpus[param] = (decl, inter, rdecl, rinter)
	results = dict((param, {'decl->inter': [], 'inter->decl': []}) for param in parameters)
	indices = range(len(treesdecl))
	samplesize = 10
	for fold in range(10):
		test = sample(filtered, samplesize)
		#test = sample(indices, samplesize)
		#test = range(len(treesdecl))[fold*10:fold*10+20]
		train = [a for a in indices if a not in test]
		assert(set(test).intersection(set(train)) == set([]))
		for param in parameters:
			treesdecl, treesinter, rtreesdecl, rtreesinter = proccorpus[param]
			assert(len(treesdecl) == len(treesinter) == len(sentsinter) == len(sentsdecl))
			corpus = [(treesdecl[a], treesinter[a]) for a in train]
			if rtreesdecl and rtreesinter:
				corpus += [(rtreesdecl[a], rtreesinter[a]) for a in train]
			tdop = TransformationDOP()
			for n, (tree1, tree2) in enumerate(corpus):
				print n
				tdop.add_to_grammar(linked_subtrees_to_probabilistic_rules(minimal_linked_subtrees(tree2, tree1), limit_subtrees=2000))
			tdop.extendlex([(treesinter[a], treesdecl[a]) for a in test])
			print "training done" 
			#matchesi1.append(run(tdop, [treesinter[a] for a in test], [sentsdecl[a] for a in test], ("foldd%d.txt" % fold), trees=True, my=True))
			filename = "results/%s-d%d.txt" % ("-".join(param), fold)
			stats = run(tdop, [sentsinter[a] for a in test], [sentsdecl[a] for a in test], filename, trees=False, my=False)
			results[param]['inter->decl'].append(stats)
			del tdop

			tdop = TransformationDOP()
			for n, (tree1, tree2) in enumerate(corpus):
				print n
				tdop.add_to_grammar(linked_subtrees_to_probabilistic_rules(minimal_linked_subtrees(tree1, tree2), limit_subtrees=2000))
			tdop.extendlex([(treesdecl[a], treesinter[a]) for a in test])
			print "training done" 
			#matchesd1.append(run(tdop, [treesdecl[a] for a in test], [sentsinter[a] for a in test], ("foldi%d.txt" % fold), trees=True, my=True))
			filename = "results/%s-i%d.txt" % ("-".join(param), fold)
			stats = run(tdop, [sentsdecl[a] for a in test], [sentsinter[a] for a in test], filename, trees=False, my=False)
			results[param]['decl->inter'].append(stats)
			del tdop
	print results, "\n\n"
	printstats()

def printstats():
	def collate(dicts):
		return dict((k, [d[k] for d in dicts]) for k in dicts[0])
	import os
	results = defaultdict(lambda: defaultdict(list))
	for a in os.listdir("results"):
		lines = open(os.path.join("results", a)).read().splitlines()[-13:]
		lines = [lines[x] for x in range(13) if x not in (8,9,10)]
		lines = [x.split(':') for x in lines]
		for x in range(3):
			lines[x][1] = lines[x][1].split("=>")[1][:-2]
		lines = [(k,float(v)) for k,v in lines]
		param, direction = a.rsplit("-", 1)
		results[param][direction[0]].append(dict(lines))
	
	print "10 folds"
	for param in results:
		for direction in results[param]:
			print '\t', " ".join(param), direction
			for key, value in collate(results[param][direction]).items():
				print "%s %s %f (%f)" % (key, " " * (40 - len(key)), mean(value), std(value))
		print
	
	out = open("results.csv", "w")
	out.write(",".join(repr(a) for a in ["parameters"] + results[results.keys()[0]]['i'][0].keys()) + '\n')
	for param in results:
		for direction in results[param]:
			out.write(", ".join([repr("-".join((param,direction)))] + map(repr, map(mean, collate(results[param][direction]).values()))) + '\n')
			# std dev?
	out.close()	

def mungetest():
	import cPickle
	mangled = cPickle.load(open("mangled.pickle","rb"))
	for (deriv, tree, notcovered), result in mangled.items():
		print "deriv", deriv
		print "tree", tree
		print "notcovered", notcovered
		print "former result", result
		print "former leaves:", " ".join(result.leaves())
		newresult = munge(deriv, tree, notcovered)
		if newresult != result:
			print "current result", newresult
			print "current leaves:", " ".join(newresult.leaves())
		print

if __name__ == '__main__':
	import doctest
	# do doctests, but don't be pedantic about whitespace
	fail, attempted = doctest.testmod(verbose=False,
	optionflags=doctest.NORMALIZE_WHITESPACE | doctest.ELLIPSIS)
	if attempted and not fail:
		print "%d doctests succeeded!" % attempted
	if argv and argv[1] and argv[1] in "printstats runexp tenfold interface mungetest test test2".split(): eval(argv[1] + '()')

