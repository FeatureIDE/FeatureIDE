===========================
Dataset: ERP System
Domain: Business Management
===========================

-------
Version
-------

	Version 1.0 (May 2016)

-----------
Description
-----------

	This dataset consists of multiple enterprise software modules (i.e., features) that are: purchase, sale, supply chain management, inventory control, finances, manufacturing, accounting, fiscal affairs, customer relationship and marketing. The ERP system integrates these various modules into one complete system to manage processes and information across the entire organization. The complete system is considered a large application as it is composed of 1.653 features.

	The product configuration is performed as a process of customization and generation of a specific product for each company employee. The company configuration strategy takes into account two activities: eliciting employees' requirements and decision-making process. The elicitation of requirements involves multiple stakeholders, while the decision-making process is conducted only by an Information Technology (IT) expert. On the one hand, the eliciting employees' requirements activity is concerned with collecting the needs of employees. This activity defines the functionalities or properties that a system must have that meet the employees' needs to perform their specific set of tasks. On the other hand, the  decision-making activity is performed interactively, mapping the target employees' requirements to features in the feature model. Finally, as a result of the process, a concrete and complete product configuration is derived and delivered to the employee.

---------------
Data statistics
---------------

    	1653 features
	171 real configurations
	> 10^9 possible valid configurations
    	approx. 7% cross-tree constraints

---------------------
Files and data format
---------------------
	
	The data is formatted one entry per line as follows (tab separated, "\t"):

	* configurations.csv
   
		userID \t featureID
		This file contain the details of configuration from each employee.
		
     
	* features.csv
   
		featureID 
        	This file contains the list of all features available in the ERP system.
			
	* ERP-System.xml
	
			This file contains the ERP system feature model in the SXFM (S.P.L.O.T.) format.
			This feature model can be imported in FeatureIDE or S.P.L.O.T. tools.
		
------- 
License
-------

	The employees' names and other personal information are not provided for this dataset.
	The data contained in ERP-System.zip is made available for non-commercial use.

----------------
Acknowledgements
----------------

	This work was supported by the National Counsel of Technological and Scientific Development - CNPq (grant 202368/2014-9).

----------
References
----------
   
	<Subject to change - The dataset is released in the 15th International Conference on Generative Programming: Concepts & Experience (GPCE'16): http://conf.researchr.org/home/gpce-2016>

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
  