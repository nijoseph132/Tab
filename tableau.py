
MAX_CONSTANTS = 10


# in a formula ( ... o ... ), it finds the main connective o
def findMiddle(s):
    count, index = 0, 1
    while index < len(s):
        if count == 0 and (
            s[index : index + 2] == "=>"
            or s[index : index + 2] == "\\/"
            or s[index : index + 2] == "/\\"
        ):
            return index
        elif s[index] == "(":
            count += 1
        elif s[index] == ")":
            count -= 1
        index += 1
    return -1

# systematically checks for a proper atomic formula: PRED(VAR,VAR)
def checkAtom(s):
    variablesAndConstants = ["x", "y", "z", "w", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j"]
    if len(s) != 6:
        return False
    elif s[1] != "(" or s[3] != "," or s[5] != ")":
        return False
    elif s[2] not in variablesAndConstants or s[4] not in variablesAndConstants:
        return False
    return True

def copyList(list):
    newList = []
    for item in list:
        newList.append(item)
    return newList

# Return the LHS of a binary connective formula
def lhs(fmla):
    middleIndex = findMiddle(fmla)
    return fmla[1:middleIndex]

# Return the connective symbol of a binary connective formula
def con(fmla):
    middleIndex = findMiddle(fmla)
    return fmla[middleIndex:middleIndex+2]

# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    middleIndex = findMiddle(fmla) 
    return fmla[middleIndex+2:len(fmla)-1]  

# returns True if formula is FOL, False if formula is propositional logic.
def isFOL(fmla):
    if ("p" in fmla or "q" in fmla or "r" in fmla or "s" in fmla):
        return False
    else:
        return True

# Parse a formula, consult parseOutputs for return values.
def parse(fmla):
    # empty formula
    if len(fmla) == 0:
        return 0

    # constant -> Propositional Logic
    elif fmla == "p" or fmla == "q" or fmla == "r" or fmla == "s":
        return 6
    
    # atom -> FOL
    elif fmla[0] == "P" or fmla[0] == "Q" or fmla[0] == "R" or fmla[0] == "S":
        if checkAtom(fmla):
            return 1
        else:
            return 0

    # negation
    elif fmla[0] == "~":
        if (parse(fmla[1:]) == 0):
            return 0
        elif (isFOL(fmla)):
            return 2
        else:
            return 7
        
    # FOL: existential quantifiers
    elif fmla[0] == "E" and (fmla[1] == "x" or fmla[1] == "y" or fmla[1] == "z" or fmla[1] == "w"):
        if (parse(fmla[2:]) == 0):
            return 0
        else:
            return 4
        
    # FOL: universal quantifiers
    elif fmla[0] == "A" and (fmla[1] == "x" or fmla[1] == "y" or fmla[1] == "z" or fmla[1] == "w"):
        if (parse(fmla[2:]) == 0):
            return 0
        else:
            return 3
        

    # brackets
    elif fmla[0] == "(" and fmla[-1] == ")":
        # find the index of the main connective
        index = findMiddle(fmla)
        if index == -1 or parse(lhs(fmla)) == 0 or parse(rhs(fmla)) == 0:
            return 0
        elif isFOL(fmla):
            return 5
        else:
            return 8

    # random characters
    else:
        return 0
    

def fullyExpanded(theory):
    if (isFOL(theory[0])):
        for fmla in theory:
            if not (checkAtom(fmla) or (fmla[0] == "~" and checkAtom(fmla[1:]))):
                return False
    else:
        expanded = ["p", "q", "r", "s", "~p", "~q", "~r", "~s"]
        for fmla in theory:
            if fmla not in expanded:
                return False
    return True

def contradict(theory):
    for fmla in theory:
        if fmla[0] == "~":
            if fmla[1:] in theory:
                return True
    return False


# You may choose to represent a theory as a set or a list
def theory(fmla):#initialise a theory with a single formula in it
    return [fmla]

#check for satisfiability
#output 0 if not satisfiable, output 1 if satisfiable, output 2 if number of constants exceeds MAX_CONSTANTS
def sat(tableau):
    newConstants = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"]
    availableConstants = []
    constantCounter = 0
    # keeps track of which constants have been used to instantiate universal quantifiers
    universalQuantifierToConstants = dict()

    index = 0
    while (len(tableau) != 0):
        index += 1
        
        currentTheory = tableau.pop(0)

        if (fullyExpanded(currentTheory)):
            if (contradict(currentTheory)):
                continue
            else:
                # one of the branches is fully expanded with no contradictions:
                return 1
        else:
            # expand the first formula in the theory
            fmla = currentTheory.pop(0)

            # Prop/Atom Case:
            if (fmla == "p" or fmla == "q" or fmla == "r" or fmla == "s" or checkAtom(fmla)):
                currentTheory.append(fmla)
                tableau.append(currentTheory)

            # Alpha Case 1: Double Negation                                 ~~
            if (fmla[0:2] == "~~"):
                currentTheory.append(fmla[2:])
                tableau.append(currentTheory)

            # Alpha Case 2: Conjunction                                    /\\
            elif (con(fmla) == "/\\"): 
                currentTheory.append(lhs(fmla))
                currentTheory.append(rhs(fmla))
                tableau.append(currentTheory)
                
            # Alpha Case 3: Negated Disjunction                           ~ \\/
            elif (fmla[0] == "~" and con(fmla[1:]) == "\\/"):
                currentTheory.append("~" + lhs(fmla[1:]))
                currentTheory.append("~" + rhs(fmla[1:]))
                tableau.append(currentTheory)

            # Alpha Case 4: Negated Implication                            ~ =>
            elif (fmla[0] == "~" and con(fmla[1:]) == "=>"):
                currentTheory.append(lhs(fmla[1:]))
                currentTheory.append("~" + rhs(fmla[1:]))
                tableau.append(currentTheory)

            # Beta Case 1: Disjunction                                     \\/
            elif (con(fmla) == "\\/"):
                newTheory = copyList(currentTheory)
                newTheory.append(lhs(fmla))
                currentTheory.append(rhs(fmla))
                tableau.append(newTheory)
                tableau.append(currentTheory)
            
            # Beta Case 2: Negated Conjunction                            ~ /\\
            elif (fmla[0] == "~" and con(fmla[1:]) == "/\\"):
                newTheory = copyList(currentTheory)
                newTheory.append("~" + lhs(fmla[1:]))
                currentTheory.append("~" + rhs(fmla[1:]))
                tableau.append(newTheory)
                tableau.append(currentTheory)

            # Beta Case 3: Implication                                      =>
            elif (con(fmla) == "=>"):
                newTheory = copyList(currentTheory)
                newTheory.append("~" + lhs(fmla))
                currentTheory.append(rhs(fmla))
                tableau.append(newTheory)
                tableau.append(currentTheory)

            # Delta Case 1: Existential Quantifier                          E
            elif (isFOL(fmla) and fmla[0] == "E"):
                constantCounter += 1
                if (constantCounter > MAX_CONSTANTS):
                    return 2
                
                variable = fmla[1]
                const = newConstants.pop(0)
                availableConstants.append(const)
                currentTheory.append(fmla[2:].replace(variable, const))
                tableau.append(currentTheory)
            
            # Delta Case 2: Negated Universal Quantifier                    ~A
            elif (isFOL(fmla) and fmla[0:2] == "~A"):
                constantCounter += 1
                if (constantCounter > MAX_CONSTANTS):
                    return 2
                
                variable = fmla[2]
                const = newConstants.pop(0)
                availableConstants.append(const)
                currentTheory.append("~" + fmla[3:].replace(variable, const))
                tableau.append(currentTheory)

            # Gamma Case 1: Universal Quantifier                             A
            elif (isFOL(fmla) and fmla[0] == "A"):
                if (availableConstants == []):
                    currentTheory.append(fmla)
                    tableau.append(currentTheory)
                    continue

                if (fmla not in universalQuantifierToConstants):
                    universalQuantifierToConstants[fmla] = []
                
                const = ""

                for c in availableConstants:
                    if (c not in universalQuantifierToConstants[fmla]):
                        const = c
                        universalQuantifierToConstants[fmla].append(c)
                        break
                
                if (const == ""):
                    tableau.append(currentTheory)
                    continue

                variable = fmla[1]
                currentTheory.append(fmla[2:].replace(variable, const))
                currentTheory.append(fmla)
                tableau.append(currentTheory)

            # Gamma Case 2: Negated Existential Quantifier                  ~E
            elif (isFOL(fmla) and fmla[0:2] == "~E"):
                if (availableConstants == []):
                    currentTheory.append(fmla)
                    tableau.append(currentTheory)
                    continue
                
                if (fmla not in universalQuantifierToConstants):
                    universalQuantifierToConstants[fmla] = []
                
                const = ""

                for c in availableConstants:
                    if (c not in universalQuantifierToConstants[fmla]):
                        const = c
                        universalQuantifierToConstants[fmla].append(c)
                        break
                
                if (const == ""):
                    tableau.append(currentTheory)
                    continue

                variable = fmla[2]
                currentTheory.append("~" + fmla[3:].replace(variable, const))
                currentTheory.append(fmla)
                tableau.append(currentTheory)
    
    return 0









#DO NOT MODIFY THE CODE BELOW
f = open('input.txt')

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']



firstline = f.readline()

PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in f:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5,8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line) ,rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
