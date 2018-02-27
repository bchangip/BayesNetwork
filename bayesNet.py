# Universidad del Valle de Guatemala
# Bryan Chan - 14469
# Query parser

import pprint
import re
from itertools import product
from graphviz import Digraph
from functools import reduce, lru_cache
from operator import mul
from copy import deepcopy

pp = pprint.PrettyPrinter()

class BayesNet(object):
	def __init__(self):
		self.queryMatch = re.compile('^P\((!)?[a-zA-Z](, (!)?[a-zA-Z])*(\|(!)?[a-zA-Z](, (!)?[a-zA-Z])*)?\)$')
		self.bayesInputMatch = re.compile('^P\((!)?[a-zA-Z](, (!)?[a-zA-Z])*(\|(!)?[a-zA-Z](, (!)?[a-zA-Z])*)?\) = (0|1)(.(\d)+)?$')

	def parseBNFile(self, filename):
		bayesDescription = []
		lineCounter = 0
		with open(filename) as f:
			for line in f:
				lineCounter += 1
				if self.bayesInputMatch.match(line):
					bayesDescription.append(line)
				else:
					print("Sintax error in line", lineCounter)
					return False

		bayesDescription = list(map(lambda x: x.strip(), bayesDescription))

		bayesNet = {}

		for description in bayesDescription:
			sentence, probability = description.split(" = ")
			probability = float(probability)
			sentence = sentence[2:-1]
			if "|" in sentence:
				subject, evidence = sentence.split("|")
				if "," not in subject:
					if "!" in subject:
						subject = subject[1:]
						probability = 1 - probability
					singleEvidences = evidence.split(", ")
					for singleEvidence in singleEvidences:
						if "!" in singleEvidence:
							singleEvidence = singleEvidence[1:]
						bayesNet[singleEvidence]["childs"].add(subject)

					if subject not in bayesNet:
						bayesNet[subject] = {
							"probabilities": {
								tuple(sorted(tuple(singleEvidences))): probability
							},
							"childs": set()
						}
					else:
						bayesNet[subject]["probabilities"][tuple(sorted(tuple(singleEvidences)))] = probability
				else:
					print("This description is not neccesary:", description)
			else:
				if "," not in sentence:
					bayesNet[sentence] = {
						"probability": probability,
						"childs": set()
					}
				else:
					print("This description is not neccesary:", description)
		self.bayesNet = bayesNet
		self.compressedForm = self.compressBayesNet()
		return True

	def verifyCompleteness(self):
		pass

	def conjunctify(self, query):
		if self.queryMatch.match(query):
			if "|" in query:
				query = query[2:-1]
				subject, evidence = query.split("|")
				resultingQuery = "P("+subject+", "+evidence+")/P("+evidence+")"
				return resultingQuery
			else:
				return query

		else:
			# print("Query malformed")
			return False

	def totalInjector(self, queryFactor, combination):
		resultingQuery = "P("+queryFactor
		if type(combination) == type(tuple()):
			for variable in combination:
				resultingQuery += ", "+variable
		else:
			resultingQuery += ", "+combination
		resultingQuery += ")"
		return resultingQuery

	def totalizeSingleQuery(self, queryFactor):
		tempQueryFactor = queryFactor[2:-1]
		queryVariables = tempQueryFactor.split(", ")
		allVariables = set([variable for variable in self.bayesNet])
		queryVariables = set(map(lambda x: x[1:] if "!" in x else x, queryVariables))

		iterationVariables = allVariables-queryVariables
		iterationSet = list(map(lambda x: list((x, "!"+x)), iterationVariables))
		if len(iterationSet) == 0:
			return queryFactor
		elif len(iterationSet) == 1:
			combinations = tuple([iterationSet[0][0],iterationSet[0][1]])
		else:
			combinations = iterationSet[0]
			for i in range(len(iterationSet)-1):
				combinations = list(product(combinations, iterationSet[i+1]))

		totalizedQuery = list(map(lambda x: self.totalInjector(tempQueryFactor, x), combinations))
		totalizedQuery = " + ".join(totalizedQuery)
		return totalizedQuery

	def totalize(self, conjunctQuery):
		if "/" in conjunctQuery:
			numerator, denominator = conjunctQuery.split("/")
			return self.totalizeSingleQuery(numerator)+"/"+self.totalizeSingleQuery(denominator)
		else:
			return self.totalizeSingleQuery(conjunctQuery)

	def draw(self):
		graph = Digraph('Bayes')
		for node in self.bayesNet:
			graph.node(node)
			for child in self.bayesNet[node]["childs"]:
				graph.edge(node, child)
		graph.view(cleanup=True)

	def compressBayesNet(self):
		factors = []
		for node in self.bayesNet:
			parents = set()
			for innerNode in self.bayesNet:
				if node in self.bayesNet[innerNode]["childs"]:
					parents.add(innerNode)
			if len(parents) == 0:
				factors.append("P("+node+")")
			else:
				factors.append("P("+node+"|"+", ".join(parents)+")")
		return " * ".join(factors)

	def totalToCompressedSingle(self, singleTotalQuery):
		singleTotalQuery = singleTotalQuery[2:-1].split(", ")
		# print("Incoming singleTotalQuery", singleTotalQuery)
		# compressedForm = self.compressBayesNet()
		compressedForm = deepcopy(self.compressedForm)
		for variable in self.bayesNet:
			for incomingVariable in singleTotalQuery:
				if variable in incomingVariable:
					compressedForm = compressedForm.replace(variable, incomingVariable)
		return compressedForm

	def totalToCompressedQuery(self, totalQuery):
		if "/" in totalQuery:
			numerator, denominator = totalQuery.split("/")
			numerator = numerator.split(" + ")
			denominator = denominator.split(" + ")

			numerator = " + ".join(map(lambda x: self.totalToCompressedSingle(x), numerator))
			denominator = " + ".join(map(lambda x: self.totalToCompressedSingle(x), denominator))

			return numerator+"/"+denominator

		else:
			numerator = totalQuery.split(" + ")
			return " + ".join(map(lambda x: self.totalToCompressedSingle(x), numerator))

	def evaluateCompressedSingle(self, compressedSingle):
		query = compressedSingle[2:-1]
		if "|" in query:
			subject, evidence = query.split("|")
			evidence = tuple(sorted(evidence.split(", ")))
			if "!" in subject:
				subject = subject[1:]
				return 1 - self.bayesNet[subject]["probabilities"][evidence]
			else:
				return self.bayesNet[subject]["probabilities"][evidence]
		else:
			if "!" in query:
				query = query[1:]
				return 1 - self.bayesNet[query]["probability"]
			else:
				return self.bayesNet[query]["probability"]

	def evaluateCompressedQuery(self, compressedQuery):
		if "/" in compressedQuery:
			numerator, denominator = compressedQuery.split("/")
			numerator = numerator.split(" + ")
			denominator = denominator.split(" + ")

			numeratorByFactors = list(map(lambda x: x.split(" * "), numerator))
			denominatorByFactors = list(map(lambda x: x.split(" * "), denominator))


			numeratorValue = list(map(
				lambda x: list(map(
					lambda y: self.evaluateCompressedSingle(y),
					x
				)),
				numeratorByFactors
			))

			denominatorValue = list(map(
				lambda x: list(map(
					lambda y: self.evaluateCompressedSingle(y),
					x
				)),
				denominatorByFactors
			))

			numeratorValue = sum(list(map(
				lambda x: reduce(mul, x),
				numeratorValue
			)))

			denominatorValue = sum(list(map(
				lambda x: reduce(mul, x),
				denominatorValue
			)))

			return numeratorValue/denominatorValue
		else:
			numerator = compressedQuery.split(" + ")

			numeratorByFactors = list(map(lambda x: x.split(" * "), numerator))

			numeratorValue = list(map(
				lambda x: list(map(
					lambda y: self.evaluateCompressedSingle(y),
					x
				)),
				numeratorByFactors
			))

			numeratorValue = sum(list(map(
				lambda x: reduce(mul, x),
				numeratorValue
			)))

			return numeratorValue

	def sanitizeQuery(self, query):
		if not self.queryMatch.match(query):
			return False
		query = query[2:-1]
		if "|" in query:
			query = query.split("|")
			allVariables = [*query[0].split(", "), *query[1].split(", ")]
		else:
			allVariables = query.split(", ")

		allVariables = list(map(lambda x: x[1:] if "!" in x else x, allVariables))
		for variable in allVariables:
			if variable not in self.bayesNet:
				return False

		return True

	# @lru_cache()
	def computeQuery(self, query):
		if self.sanitizeQuery(query):
			conjunctQuery = self.conjunctify(query)
			totalized = self.totalize(conjunctQuery)
			compressedQuery = self.totalToCompressedQuery(totalized)
			return self.evaluateCompressedQuery(compressedQuery)
		else:
			return "Invalid query"

	def simulateQuery(self, query):
		if self.sanitizeQuery(query):
			return "Should simulate query"
		else:
			return "Invalid query"	





bayesNet = BayesNet()
bayesNet.parseBNFile("bayesnet.bn")
# bayesNet.draw()
# bayesNet = parseBNFile("bayesnet.bn")
# bayesNet = parseBNFile("parcialNet.bn")
# drawBayesNet(bayesNet)
for i in range(10):
	print(bayesNet.computeQuery("P(A)"))
	print(bayesNet.computeQuery("P(A, B)"))
	print(bayesNet.computeQuery("P(A|B)"))
	print(bayesNet.computeQuery("P(A|C)"))
	print(bayesNet.computeQuery("P(C)"))
	print(bayesNet.computeQuery("P(A|B)"))
	print(bayesNet.computeQuery("P(C|B)"))

for i in range(10):
	print(bayesNet.simulateQuery("P(A)"))
	print(bayesNet.simulateQuery("P(A, B)"))
	print(bayesNet.simulateQuery("P(A|B)"))
	print(bayesNet.simulateQuery("P(A|C)"))
	print(bayesNet.simulateQuery("P(C)"))
	print(bayesNet.simulateQuery("P(A|B)"))
	print(bayesNet.simulateQuery("P(C|B)"))

# while True:
# 	queryInput = input("Enter your query: ")
# 	print("Result:", bayesNet.computeQuery(queryInput))
	# conjunctQuery = conjunctify(queryInput)
	# # pp.pprint(bayesNet)
	# # print("Totalized bayes net:", compressBayesNet(bayesNet))
	# # conjunctQuery = conjunctify("P(!B|A)")
	# print("conjunctQuery", conjunctQuery)
	# totalized = totalize(bayesNet, conjunctQuery)
	# print("Totalized", totalized)
	# compressedQuery = totalToCompressedQuery(bayesNet, totalized)
	# print("compressedQuery: ", compressedQuery)
	# # print(evaluateCompressedSingle(bayesNet, "P(!B)"))
	# print("Result: ", evaluateCompressedQuery(bayesNet, compressedQuery))



'''
bayesNet = {
	"A": {
		"childs": ["C"],
		"probability": 0.3
	},
	"B": {
		"childs": ["C"],
		"probability": 0.23
	},
	"C": {
		"childs": [],
		"probabilities": {
			("A","B"): 0.2,
			("!A","B"): 0.1,
			("A","!B"): 0.77,
			("!A","!B"): 0.5
		}
	}
}
'''