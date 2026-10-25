#!/usr/bin/env python3
"""Exact row evaluator also sharing inverse linear forms across terms."""
from pathlib import Path
import hashlib, json, random

HERE = Path(__file__).parent


class Evaluator:
    def __init__(self):
        self.point = self.prime = None
        self.terms, self.forms, self.inverses, self.coefficients = {}, {}, {}, {}

    def __call__(self, expression, point, prime=1000003):
        point = tuple(point)
        if (point, prime) != (self.point, self.prime):
            if prime != self.prime:
                self.coefficients.clear()
            self.point, self.prime = point, prime
            self.terms.clear(); self.forms.clear(); self.inverses.clear()

        def value(form):
            if form not in self.forms:
                self.forms[form] = (sum(a*b for a, b in zip(form[:-1], point))+form[-1]) % prime
            return self.forms[form]

        total = 0
        for key, coefficient in expression.items():
            if key not in self.terms:
                numerator, power, denominator = key
                term = pow(value(numerator), power, prime)
                for form, multiplicity in denominator:
                    if form not in self.inverses:
                        q = value(form)
                        if not q:
                            raise ZeroDivisionError
                        self.inverses[form] = pow(q, -1, prime)
                    term = term*pow(self.inverses[form], multiplicity, prime) % prime
                self.terms[key] = term
            if coefficient not in self.coefficients:
                self.coefficients[coefficient] = coefficient.numerator*pow(coefficient.denominator, -1, prime) % prime
            total = (total+self.coefficients[coefficient]*self.terms[key]) % prime
        return total


def main():
    import overnight_upper_triangle_attachments as attachment
    import overnight_upper_triangle_fixed as fixed
    import overnight_upper_product_family as base
    data = json.loads((HERE/'overnight_upper_triangle_ear_7.json').read_text())
    base.raw_chain = attachment.raw_chain
    base.group = fixed.group
    columns = [base.expression(base.sym_chain(7, d)) for d in data['descriptors'][::40]]
    rng = random.Random(251042)
    evaluator = Evaluator()
    checks = 0
    for prime in (1000003, 1000000007):
        for _ in range(3):
            point = tuple(rng.randrange(1, 1000) for _ in range(5))
            for column in columns:
                for expression in column.values():
                    try:
                        expected = base.evaluate(expression, point, prime)
                    except ZeroDivisionError:
                        continue
                    assert evaluator(expression, point, prime) == expected
                    checks += 1
    result = dict(status='EXACT_INVERSE_FORM_CACHE_CONTROLS_PASS', checks=checks,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (HERE/'overnight_upper_modular_cache2.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result, flush=True)


if __name__ == '__main__':
    main()
