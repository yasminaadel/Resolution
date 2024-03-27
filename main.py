def eliminate_implication(expression):
    def left_expression(expression, imply):
        brackets_count = 0
        i = imply - 1  # starts the search from one position to the left of imply
        while i >= 0:  # stop when it reaches the beginning of the string
            if expression[i] == ')':
                brackets_count += 1
            elif expression[i] == '(':
                brackets_count -= 1  # says that bracket is closed
                # checks if we exited a full balanced set of brackets
                if brackets_count == -1:
                    # checks if the two characters before i is a quantifier
                    if i >= 2 and expression[i - 2:i] in ['∀', '∃']:
                        return i-2  # update boundary to include quantifier to make it part pf the expression
                    return i
            # check if all opened brackets are closed
            # and we are at the begining of the strong or we are at a logical operator or bracket
            elif brackets_count == 0 and (i == 0 or expression[i - 1] in ['∧', '∨', '(', '∀', '∃']):
                return i
            i -= 1
        return 0  # if not finding any boundary

    def right_expression(expression, imply):
        brackets_count = 0
        i = imply  # starts the search from one position after imply
        while i < len(expression):
            if expression[i] == '(':
                brackets_count += 1
            elif expression[i] == ')':
                brackets_count -= 1
            # search if there exist any operators because it represents a boundary for right expression
            elif brackets_count == 0 and expression[i] in ['∧', '∨']:
                return i-1  # index just before operator, end of expression
            i += 1
        return len(expression)-1  # index of the last character in expression

    i = 0
    while i < len(expression):
        if expression[i:i + 2] == '->':  # checks if imply sign found
            # determine left and right expressions
            left_start = left_expression(expression, i)
            right_end = right_expression(expression, i + 2)
            # get left and right hand side expressions
            # strip() is used to remove any extra whitespace
            left_expr = expression[left_start:i].strip()
            right_expr = expression[i + 2:right_end + 1].strip()
            # transform expression
            change_expression = f"¬{left_expr} ∨ {right_expr}"
            # update the original expression with the new one
            expression = expression[:left_start] + change_expression + expression[right_end + 1:]
            # updates index of i to check the new expression if it has any other implications
            i = left_start + len(change_expression) - (right_end - left_start + 1)
        else:  # if there is no implication
            i += 1
    return expression


def move_negation_inward(expression):
    expression = expression.replace("~(", "¬(")
    expression = expression.replace("¬(¬", "(")  # remove double negations

    def check_quantifiers(expression):
        result = ""
        i = 0
        while i < len(expression):
            # checks if the current position starts with ¬∀ or ¬∃
            if expression.startswith("¬∀", i) or expression.startswith("¬∃", i):
                quantifier = '∃' if expression[i + 1] == '∀' else '∀'  # switch quantifiers
                result += quantifier  # adds the switched quantifier to the result
                i += 2  # increment i to be after quantifier
                var = expression[i]  # var is the char at current position (the one after quantifier)
                result += var + "¬"  # move negation inside to the variable of expression after quantifier
                i += 1
            else:
                result += expression[i]
                i += 1
        return result

    def de_morgans(expression):
        #  ¬(A ∧ B) = ¬A ∨ ¬B
        #  ¬(A ∨ B) = ¬A ∧ ¬B
        while '¬(' in expression:
            start = expression.find('¬(') + 2  # find begining of expression
            brackets_count = 1
            i = start
            # loops until reaching end of bracket
            while i < len(expression) and brackets_count != 0:
                if expression[i] == '(':
                    brackets_count += 1
                elif expression[i] == ')':
                    brackets_count -= 1
                i += 1
            end_index = i
            # expression inside bracket
            inner_expression = expression[start:end_index - 1]

            transformed = ""
            if '∧' in inner_expression:
                # replace ∧ with ∨ and negating each term
                terms = inner_expression.split('∧')  # separates terms by the operator
                replaced_terms = ["¬" + term for term in terms]
                transformed = " ∨ ".join(replaced_terms)  # join them by the or
            elif '∨' in inner_expression:
                # replace ∨ with ∧ and negating each term
                terms = inner_expression.split('∨')
                replaced_terms = ["¬" + term for term in terms]
                transformed = " ∧ ".join(replaced_terms)
            else:
                if inner_expression.startswith("¬"):
                    transformed = inner_expression[1:]  # remove the negation (double negation)
                else:
                    transformed = "¬" + inner_expression
            # update expression with the new one
            expression = expression[:start - 2] + transformed + expression[end_index:]

        return expression

    expression = check_quantifiers(expression)
    expression = de_morgans(expression)
    return expression


def remove_double_negation(expression):
    # remove double negation
    while '¬¬' in expression:
        expression = expression.replace('¬¬', '')
    return expression


def standardize_variables(expressions):
    if isinstance(expressions, list):
        # Join the list into a single string if a list is passed, assuming list items are separated by ', '
        expressions = "', '".join(expressions)
    # handle case if more than one expression is entered
    expressions = expressions.split("', '")
    # store expressions after standardizing variables
    standardized_expressions = []

    for expression in expressions:
        new_expression = expression  # make a copy to prevents altering original one
        used_variables = set()  # avoid using a variable name twice
        replaced = {}  # map original variable name to new one

        # generate new variable name
        def new_variable(old_variable):
            if old_variable in replaced:  # if already mapped get new name from map
                return replaced[old_variable]

            # generate new name alphabetically
            new_variable = chr(ord('a') + len(used_variables))
            # make sure variable name is not used before
            while new_variable in used_variables:
                new_variable = chr(ord(new_variable) + 1)
            # add new name to used and replaced
            used_variables.add(new_variable)
            replaced[old_variable] = new_variable
            return new_variable

        i = 0
        while i < len(new_expression):
            if new_expression[i] in "∀∃":
                variable = new_expression[i+1]
                if variable.islower():  # check if it is a variable
                    new_var = new_variable(variable)  # get new name
                    # replace this variable throughout the expression.
                    new_expression = new_expression[:i+1] + new_expression[i+1:].replace(variable, new_var)
                    # don't check the new replaced part to avoid checking it again
                    i += len(new_var) - 1
            i += 1

        standardized_expressions.append(new_expression)

    # join expressions again
    return "', '".join(standardized_expressions)


def prenex(expression):
    # handle case if more than one expression is entered
    expression = expression.split("', '")
    # store expressions after moving all quantifiers
    prenex_expressions = []

    for expression in expression:
        quantifiers = ""
        remaining = expression

        # loop until no quantifiers present in remaining part
        while "∀" in remaining or "∃" in remaining:
            for quantifier in ["∀", "∃"]:
                position = remaining.find(quantifier)  # return -1 if not found
                # checks if quantifier is found
                if position != -1:
                    variable = remaining[position + 1]   # character following the quantifier
                    # move quantifier and its variable to the beginning
                    quantifiers += remaining[position:position + 2] + " "
                    # delete the quantifier and variable from the remaining
                    remaining = remaining[:position] + remaining[position + 2:]

        # add the quantifiers to the remaining of the expression
        prenex_expression = quantifiers + remaining
        prenex_expressions.append(prenex_expression)

    # join the processed expressions back
    return "', '".join(prenex_expressions)


def skolemize(expression):
    universal_variables = []  # store universal variables
    functions = {}  # store skolem functions
    used_variables = set()  # avoid using variables in functions twice

    i = 0
    new_expression = ""
    while i < len(expression):
        if expression[i] in ["∀", "∃"]:
            # if character is a quantifier add it and its variable
            quantifier = expression[i]
            variable = expression[i + 1]
            if quantifier == "∀":
                # add to list and string
                universal_variables.append(variable)
                # no change in the quantifier
                new_expression += f"{quantifier}{variable} "
            else:  # quantifier is ∃
                # check if there are any universal variables
                if universal_variables:
                    for u_variable in universal_variables:
                        # use first unused variable to create a term using it
                        # skolem term= f(universal variable)
                        if u_variable not in used_variables:
                            skolem_term = f"f({u_variable})"
                            used_variables.add(u_variable)  # add it to used set
                            break
                    else:
                        # if all universal variables are used, use a default naming scheme
                        skolem_term = f"f(default)"
                else:   # if there are no universal variables
                    skolem_term = "u"  # use constant
                # add variable and its skolem term in the functions dictionary
                functions[variable] = skolem_term
            i += 3  # move past the quantifier and variable
            continue
        # if character at i is an existential variable that has a term in dictionary
        elif expression[i] in functions:
            # replace existential variables with their skolem terms
            variable = expression[i]
            skolem_term = functions[variable]
            new_expression += skolem_term  # add the term to new expression
            i += 1
        #  if not a quantifier
        else:
            # add other characters to the new expression
            new_expression += expression[i]
            i += 1

    return new_expression


def eliminate_universal_quantifiers(expression):
    # handle case if more than one expression is entered
    expressions = expression.split("', '")
    new_expressions = []  # store modified expressions

    for expression in expressions:
        new_expr = ''  # empty string to store new expression
        i = 0
        while i < len(expression):
            if expression[i] == '∀':
                i += 3  # ignore the ∀ and the variable and the space
            # if not a universal quantifier
            else:
                # add character to new expression string
                new_expr += expression[i]
                i += 1
        new_expressions.append(new_expr.strip())

    # join the processed expressions back
    return "', '".join(new_expressions)


def remove_extra_brackets(expression):
    # check if expression starts with open brackets and end with end ones
    # check if brackets count are equal
    while expression.startswith('(') and expression.endswith(')') and expression.count('(') == expression.count(')'):
        possible_extra = expression[1:-1]  # remove outermost brackets
        # insure there is no unmatched brackets
        if possible_extra.count('(') == possible_extra.count(')'):
            expression = possible_extra
        else:
            break
    return expression


def cnf_single(expression):
    # already in CNF, return expression
    if "∨" not in expression:
        return remove_extra_brackets(expression)
    # when or first appears splits expression into 2 parts
    parts = expression.split("∨", 1)
    left = remove_extra_brackets(parts[0].strip())
    right = remove_extra_brackets(parts[1].strip())
    # split write part according to and operator
    conjuncts = [remove_extra_brackets(conj.strip()) for conj in right.split("∧")]
    # list to store cnf expressions
    cnf = []
    for conjunct in conjuncts:
        cnf_expression = f"({left} ∨ {conjunct})"
        cnf.append(remove_extra_brackets(cnf_expression))

    return " ∧ ".join(cnf)


def cnf(expression):
    # splitting the input into individual expressions using commas
    expressions = expression.split("' , '")
    # applying CNF single function to each expression
    cnf_expressions = [cnf_single(expr.strip("'")) for expr in expressions]
    # joining the expressions back into a single string
    return "' , '".join(cnf_expressions)



def clauses_set(expression):
    # checks if the expression is an instance of a list
    if isinstance(expression, list):
        expression = "', '".join(expression)

    def split_and(expression):
        clauses = []  # empty list to store the clauses
        current_clause = []  # empty list clauses to store the characters of the current clause being processed
        brackets_depth = 0
        for expr in expression:
            if expr == '(':
                brackets_depth += 1
            elif expr == ')':
                brackets_depth -= 1
            #  current clause has ended
            elif expr == '∧' and brackets_depth == 0:
                # characters in current_clause are joined into a string
                clauses.append(''.join(current_clause).strip())
                # reset to an empty list
                current_clause = []
                continue
            # char belongs to current clause
            current_clause.append(expr)

        # if there is any remaining clauses it is joined into a string
        if current_clause:
            clauses.append(''.join(current_clause).strip())

        return clauses

    # check if the expression has an AND operator
    if '∧' in expression:
        clauses = split_and(expression)
    else:
        # the entire expression is a single clause
        clauses = [expression]

    # Remove duplicate clauses while maintaining order
    clause_set = sorted(set(clauses), key=clauses.index)
    return clause_set


def rename_variables_in_clauses(expressions):
    variable_counter = {}  # dictionary that stores the count of each variable
    renamed_expressions = []  # list that will store the expressions renamed variables

    for expression in expressions:
        expression_variables = {}  # dictionary to avoid using same name twice
        new_expression = ""  # expression with renamed variables
        i = 0
        while i < len(expression):
            current = expression[i]  # current character in the expression
            if current.islower():  # variables are low case characters
                # check if variable has not been used already
                if current not in expression_variables:
                    # generate a new variable name
                    if current in variable_counter:
                        variable_counter[current] += 1
                    # if not found in variables counter it is added with starting count of 1
                    else:
                        variable_counter[current] = 1
                    #  add count of variable to its name ex:a1, a2,...
                    new_variable = f"{current}{variable_counter[current]}"
                    # update original variable name with its new name
                    expression_variables[current] = new_variable
                else:
                    new_variable = expression_variables[current]
                # build new expression
                new_expression += new_variable
            # if not a variable, add it to expression without changes
            else:
                new_expression += current
            i += 1
        # add to list
        renamed_expressions.append(new_expression)

    return sorted(set(renamed_expressions), key=renamed_expressions.index)


def print_clauses(expression):
    # If the input is a list, join its elements into a string using commas
    if isinstance(expression, list):
        expression = ', '.join(expression)

    # Split the expression into clauses based on commas and print each
    clauses = expression.split(',')
    for clause in clauses:
        cleaned_clause = clause.replace(",", "").replace("'", "")
        cleaned_clause = cleaned_clause.strip()
        print(cleaned_clause)


def resolution(clauses):
    # empty set to store predicates in clause
    predicates = set()
    for clause in clauses:
        # split clause into individual predicates
        predicates.update(clause.split())

    # Track changes to see if any resolution occurs
    changed = True
    while changed:
        changed = False
        for predicate in list(predicates):
            # If the negation of the current predicate exists, remove both
            if predicate.startswith("¬"):
                opposite = predicate[1:]
            else:
                opposite = "¬" + predicate

            if opposite in predicates:
                predicates.remove(predicate)
                predicates.remove(opposite)
                changed = True
                break  # Restart since we modified the set during iteration

    # If all are resolved, it's satisfiable; otherwise, it's not
    return len(predicates) == 0


if __name__ == "__main__":
    expression = "'P(x) ∨ ¬S(x) ∨ H(x)' , '∀y(R(y)->S(y))' , '(R(j) ∧ ¬P(j))' , '∀z(H(z)->E(z)' , '¬∃w(E(w)'"
    # expression = "∀x(B(x)->(∃y (Q(x,y)∧¬P(y)) ∧ (¬∃y(Q(x,y)∧Q(y, x))) ∧ ∀y(¬B(y)->¬E(x,y))))"
    print("Original expression:", expression)
    step1 = eliminate_implication(expression)  # Transform implications if any.
    print("After eliminating implications:", step1)
    step2 = move_negation_inward(step1)  # Move negations inward.
    print("After moving negation inward:", step2)
    step3 = remove_double_negation(step2)  # Remove double negations.
    print("After removing double negations:", step3)
    step4 = standardize_variables(step3)  # Remove double negations.
    print("After standardizing expressions:", step4)
    step5 = prenex(step4)
    print("After converting to prenex form:", step5)
    step6 = skolemize(step5)
    print("After skolemization for existential quantifiers:", step6)
    step7 = eliminate_universal_quantifiers(step6)
    print("After eliminating universal quantifiers:", step7)
    step8 = cnf(step7)
    print("After converting to conjunctive normal form:", step8)
    step9 = clauses_set(step8)
    print("Clauses as a set:", step9)
    step10 = rename_variables_in_clauses(step9)
    print("After renaming variables so no clause shares the same variable name:", step10)
    print_clauses(step10)
    step11 = resolution(step10)
    print("Final result:", step11)