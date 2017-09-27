=======================
Dataset: E-Agribusiness
Domain: E-Commerce
=======================

-------
Version
-------

	Version 1.0 (May 2016)

-----------
Description
-----------

	This dataset represents variability from the electronic marketplaces in the agribusiness domain. It consists two types of e-commerce transactions: Business-to-Business (B2B) and Business-to-Consumer (B2C) transactions. While B2B transactions are conducted between dealers enterprises, B2C are conducted between final consumers. The complete E-Agribusiness system is considered a large application as it is composed of 2008 features. It integrates these various features for direct sales of agribusiness products to customers (i.e., final consumers and dealers enterprises). The product configuration is performed as a process of customization and generation of a specific configuration for each final consumer or dealer enterprise. For this dataset, only about 10% of the data are from final consumers, the others 90% are from dealers enterprises.

---------------
Data statistics
---------------

    	2008 features
	5749 real configurations
	> 10^9 possible valid configurations
    	none cross-tree constraints

---------------------
Files and data format
---------------------
	
	The data is formatted one entry per line as follows (tab separated, "\t"):

	* configurations.csv
   
		userID \t featureID
		This file contain the details of configuration from each customer.
		
     
	* features.csv
   
		featureID 
        	This file contains the list of all features available in the e-commerce system.
			
	* E-Agribusiness.xml
	
			This file contains the E-Agribusiness feature model in the SXFM (S.P.L.O.T.) format.
			This feature model can be imported in FeatureIDE or S.P.L.O.T. tools.
		
------- 
License
-------

	The customers' names and other personal information are not provided for this dataset.
	The data contained in E-Agribusiness.zip is made available for non-commercial use.

----------------
Acknowledgements
----------------

	This work was supported by the National Counsel of Technological and Scientific Development - CNPq (grant 202368/2014-9).

----------
References
----------
   
	- The dataset is released in the 15th International Conference on Generative Programming: Concepts & Experience (GPCE'16): http://conf.researchr.org/home/gpce-2016

    	When using this dataset you should cite:
	
		- @inproceedings{PMK+:GPCE16,
			title={A feature-based personalized recommender system for product-line configuration},
			author={Pereira, Juliana Alves and Matuszyk, Pawel and Krieter, Sebastian and Spiliopoulou, Myra and Saake, Gunter},
			booktitle={Proceedings of the International Conference on Generative Programming: Concepts and Experiences},
			pages={120--131},
			year={2016},
			organization={ACM}
		}

-------
Credits
-------

	This dataset was built by our employee contact in the company.
   
-------   
Contact
-------

   	Juliana Alves Pereira, juliana.alves-pereira@ovgu.de
  