#!/usr/bin/env python

import os
import sys

try:
    from setuptools import setup
except ImportError:
    from distutils.core import setup


if sys.argv[-1] == 'publish':
    os.system('python setup.py sdist upload')
    sys.exit()

readme = open('README.rst').read()
doclink = """
Documentation
-------------

The full documentation is at http://blinkenlights.rtfd.org."""
history = open('HISTORY.rst').read().replace('.. :changelog:', '')

setup(
    name='blinkenlights',
    version='0.1.0',
    description='Blinkenlights for C based on the theory of abstract interpretation',
    long_description=readme + '\n\n' + doclink + '\n\n' + history,
    author='Jacob Salzberg',
    author_email='jss9879@nyu.edu',
    url='https://github.com/jsalzbergedu/blinkenlights',
    packages=[
        'blinkenlights',
    ],
    package_dir={'blinkenlights': 'blinkenlights'},
    include_package_data=True,
    install_requires=[
        'pycparser>=2.21'
    ],
    license='MIT',
    zip_safe=False,
    keywords='blinkenlights',
    classifiers=[
        'Development Status :: 2 - Pre-Alpha',
        'Intended Audience :: Developers',
        'License :: OSI Approved :: MIT License',
        'Natural Language :: English',
        'Programming Language :: Python :: 2',
        'Programming Language :: Python :: 2.6',
        'Programming Language :: Python :: 2.7',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.3',
        'Programming Language :: Python :: Implementation :: PyPy',
    ],
)
