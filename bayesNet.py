# Universidad del Valle de Guatemala
# Bryan Chan - 14469
# Bayes networks

import pprint
import re
from itertools import product, chain
from graphviz import Digraph
from functools import reduce, lru_cache
from operator import mul
from copy import deepcopy

pp = pprint.PrettyPrinter()

class BayesNet(object):
    def __init__(self):
        self.queryMatch = re.compile('^P\((!)?[a-zA-Z]+(, (!)?[a-zA-Z]+)*(\|(!)?[a-zA-Z]+(, (!)?[a-zA-Z]+)*)?\)$')
        self.bayesInputMatch = re.compile('^P\((!)?[a-zA-Z]+(, (!)?[a-zA-Z]+)*(\|(!)?[a-zA-Z]+(, (!)?[a-zA-Z]+)*)?\) = (0|1)(.(\d)+)?$')

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

        bayesDescription = map(lambda x: x.strip(), bayesDescription)

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
                        if singleEvidence not in bayesNet:
                            bayesNet[singleEvidence] = {
                                "probability": None,
                                "probabilities": {},
                                "childs": set()
                            }
                        bayesNet[singleEvidence]["childs"].add(subject)
                            

                    if subject not in bayesNet:
                        bayesNet[subject] = {
                            "probability": None,
                            "probabilities": {
                                tuple(sorted(singleEvidences)): probability
                            },
                            "childs": set()
                        }
                    else:
                        bayesNet[subject]["probabilities"][tuple(sorted(singleEvidences))] = probability
                else:
                    print("This description is not neccesary:", description)
            else:
                if "," not in sentence:
                    if sentence not in bayesNet:
                        bayesNet[sentence] = {
                            "probability": probability,
                            "childs": set()
                        }
                    else:
                        bayesNet[sentence]["probability"] = probability
                else:
                    print("This description is not neccesary:", description)
        pp.pprint(bayesNet)
        self.bayesNet = bayesNet
        if self.verifyCompleteness():
            self.compressedForm = self.compressBayesNet()
            return True
        print("The bayes network description is not complete.")
        return False

    def compressBayesNet(self):
        factors = []
        for node in self.bayesNet:
            parents = set()
            for innerNode in self.bayesNet:
                if node in self.bayesNet[innerNode]["childs"]:
                    parents.add(innerNode)
            if len(parents) == 0:
                factors.append("P({})".format(node))
            else:
                factors.append("P({}|{})".format(node, ", ".join(parents)))
        return " * ".join(factors)

    def variations(self, variables):
        variations = map(lambda x: bin(x).split("b")[1], range(2**(len(variables))))
        variations = list(map(lambda x: "0"*(len(variables) - len(x))+x, variations))

        def zipVariation(booleanVariation):
            variation = []
            for i in range(len(booleanVariation)):
                if booleanVariation[i] == "0":
                    variation.append(variables[i])
                else:
                    variation.append("!"+variables[i])
            return tuple(variation)

        return list(map(
            lambda x: zipVariation(x),
            variations
        ))

    def verifyCompleteness(self):
        def verifyDependencies(node):
            # print("Check node", node)
            parents = list(filter(lambda x: node in self.bayesNet[x]["childs"], self.bayesNet.keys()))
            if len(parents):
                parentsCompleteness = all(map(lambda x: verifyDependencies(x), parents))

                # Check node completeness
                return all(map(lambda x: tuple(sorted(x)) in self.bayesNet[node]["probabilities"], self.variations(parents))) and parentsCompleteness
            else:
                return self.bayesNet[node]["probability"] != None

        leafs = filter(lambda x: len(self.bayesNet[x]["childs"]) == 0, self.bayesNet.keys())
        return all(map(lambda x: verifyDependencies(x), leafs))

    def sanitizeQuery(self, query):
        if not self.queryMatch.match(query):
            return False
        query = query[2:-1]
        if "|" in query:
            query = query.split("|")
            allVariables = [*query[0].split(", "), *query[1].split(", ")]
        else:
            allVariables = query.split(", ")

        allVariables = map(lambda x: x[1:] if "!" in x else x, allVariables)
        for variable in allVariables:
            if variable not in self.bayesNet:
                return False

        return True

    def conjunctify(self, query):
        if self.queryMatch.match(query):
            if "|" in query:
                query = query[2:-1]
                subject, evidence = query.split("|")
                resultingQuery = "P({0}, {1})/P({1})".format(subject, evidence)
                return resultingQuery
            else:
                return query

        else:
            # print("Query malformed")
            return False

    def totalize(self, conjunctQuery):
        def totalizeSingleQuery(queryFactor):
            def totalInjector(queryFactor, combination):
                resultingQuery = "P("+queryFactor
                if type(combination) == type(tuple()):
                    for variable in combination:
                        resultingQuery += ", "+variable
                else:
                    resultingQuery += ", "+combination
                resultingQuery += ")"
                return resultingQuery

            tempQueryFactor = queryFactor[2:-1]
            queryVariables = tempQueryFactor.split(", ")
            allVariables = set([variable for variable in self.bayesNet])
            queryVariables = set(map(lambda x: x[1:] if "!" in x else x, queryVariables))

            iterationVariables = list(allVariables-queryVariables)

            totalizedQuery = map(lambda x: totalInjector(tempQueryFactor, x), self.variations(iterationVariables))
            totalizedQuery = " + ".join(totalizedQuery)
            return totalizedQuery

        if "/" in conjunctQuery:
            numerator, denominator = conjunctQuery.split("/")
            return "{}/{}".format(totalizeSingleQuery(numerator), totalizeSingleQuery(denominator))
        else:
            return totalizeSingleQuery(conjunctQuery)

    def totalToCompressedQuery(self, totalQuery):
        def totalToCompressedSingle(singleTotalQuery):
            singleTotalQuery = singleTotalQuery[2:-1].split(", ")
            compressedForm = deepcopy(self.compressedForm)
            for variable in self.bayesNet:
                for incomingVariable in singleTotalQuery:
                    if variable in incomingVariable:
                        compressedForm = compressedForm.replace(variable, incomingVariable)
            return compressedForm

        if "/" in totalQuery:
            numerator, denominator = totalQuery.split("/")
            numerator = numerator.split(" + ")
            denominator = denominator.split(" + ")

            numerator = " + ".join(map(lambda x: totalToCompressedSingle(x), numerator))
            denominator = " + ".join(map(lambda x: totalToCompressedSingle(x), denominator))

            return "{}/{}".format(numerator, denominator)

        else:
            numerator = totalQuery.split(" + ")
            return " + ".join(map(lambda x: totalToCompressedSingle(x), numerator))

    def evaluateCompressedQuery(self, compressedQuery):
        def evaluateCompressedSingle(compressedSingle):
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

        if "/" in compressedQuery:
            numerator, denominator = compressedQuery.split("/")
            numerator = numerator.split(" + ")
            denominator = denominator.split(" + ")

            numeratorByFactors = map(lambda x: x.split(" * "), numerator)
            denominatorByFactors = map(lambda x: x.split(" * "), denominator)


            numeratorValue = map(
                lambda x: map(
                    lambda y: evaluateCompressedSingle(y),
                    x
                ),
                numeratorByFactors
            )

            denominatorValue = map(
                lambda x: map(
                    lambda y: evaluateCompressedSingle(y),
                    x
                ),
                denominatorByFactors
            )

            numeratorValue = sum(map(
                lambda x: reduce(mul, x),
                numeratorValue
            ))

            denominatorValue = sum(map(
                lambda x: reduce(mul, x),
                denominatorValue
            ))

            return numeratorValue/denominatorValue
        else:
            numerator = compressedQuery.split(" + ")

            numeratorByFactors = map(lambda x: x.split(" * "), numerator)

            numeratorValue = map(
                lambda x: map(
                    lambda y: evaluateCompressedSingle(y),
                    x
                ),
                numeratorByFactors
            )

            numeratorValue = sum(map(
                lambda x: reduce(mul, x),
                numeratorValue
            ))

            return numeratorValue

    def draw(self):
        graph = Digraph('Bayes')
        for node in self.bayesNet:
            graph.node(node)
            for child in self.bayesNet[node]["childs"]:
                graph.edge(node, child)
        graph.view(cleanup=True)

    def computeQuery(self, query):
        if self.sanitizeQuery(query):
            conjunctQuery = self.conjunctify(query)
            # print("conjunctQuery", conjunctQuery)
            totalized = self.totalize(conjunctQuery)
            # print("totalizedQuery", totalized)
            compressedQuery = self.totalToCompressedQuery(totalized)
            # print("compressedQuery", compressedQuery)
            return self.evaluateCompressedQuery(compressedQuery)
        else:
            return "Invalid query"

    def simulateQuery(self, query):
        if self.sanitizeQuery(query):
            return "Should simulate query"
        else:
            return "Invalid query"  

bayesNet = BayesNet()
# bayesNet.parseBNFile("bayesnet.bn")
if bayesNet.parseBNFile("layeredNet.bn"):
    bayesNet.draw()
    print("Compact form ", bayesNet.compressedForm)
    # bayesNet = parseBNFile("bayesnet.bn")
    # bayesNet = parseBNFile("parcialNet.bn")
    # drawBayesNet(bayesNet)
    # for i in range(1000):
    #   bayesNet.computeQuery("P(A)")
    #   bayesNet.computeQuery("P(A, B)")
    #   bayesNet.computeQuery("P(A|B)")
    #   bayesNet.computeQuery("P(A|C)")
    #   bayesNet.computeQuery("P(C)")
    #   bayesNet.computeQuery("P(A|B)")
    #   bayesNet.computeQuery("P(C|B)")

    # print("Finished")
    while True:
        queryInput = input("Enter your query: ")
        print("Result:", bayesNet.computeQuery(queryInput))



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