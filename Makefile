# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>


all:
	python main.py

test:
	python -c "import tests.test_basic_endofunctor ; import unittest ; unittest.main(tests.test_basic_endofunctor) ;"

clean:
	find . -name '*.pyc' | xargs rm -f

profile:
	python profile.py > /tmp/fantasia_profile.txt
