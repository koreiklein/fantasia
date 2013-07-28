# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>


all:
	python main.py

fast:
	python -O main.py

test:
	python -c "import tests.complete_suite ; tests.complete_suite.run() ;"

clean:
	find . -name '*.pyc' | xargs rm -f
	find . -name '*.pyo' | xargs rm -f

profile:
	python profile.py > /tmp/fantasia_profile.txt
