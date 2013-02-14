# Copyright (C) 2013 Korei Klein <korei.klein1@gmail.com>

all:
	python main.py

clean:
	find . -name '*.pyc' | xargs rm -f
