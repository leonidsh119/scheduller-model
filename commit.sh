#!/bin/bash

git add .

if [ -z "$0" ]
then
	git commit -m "fix"
else
	git commit -m "$0"
fi

git push
