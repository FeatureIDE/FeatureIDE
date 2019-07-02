pipeline {
    
    agent any
    
    tools {
        maven 'Maven 3.5.2'
    }

    stages {
        stage ('Initialize') {
            steps {  
                script {
                    currentBuild.displayName = "${BUILD_NUMBER} ${GIT_BRANCH} ${CAUSE}"
                }
      			sh '''
               		echo "PATH = ${PATH}"
               		echo "M2_HOME = ${M2_HOME}"
               	'''
            }
        }

        stage ('Test') {
            steps {
                sh 'mvn clean test' 
            }
        }

        stage ('Package') {
        	steps {
        		sh 'mvn clean package'
        	}
        }

        stage ('Verify') {
        	steps {
                wrap([$class: 'Xvfb']) {
                    sh 'mvn clean verify'
                }
        	}
        }

    }
}
